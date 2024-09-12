/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import ProofChecker.Checker.CheckerCore

open LeanSAT

/-! Faster CPOG parser module.
Attempt 2: hand-rolled Nat parser, inlining, and hand-passed variables instead of StateM. -/

@[inline] def isWhitespace (c : UInt8) : Bool :=
  -- TODO: check the constants are folded
  c == ' '.val.toUInt8 || c == '\t'.val.toUInt8 || c == '\r'.val.toUInt8 || c == '\n'.val.toUInt8

@[inline] def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

abbrev ParserM := Except String

/-- Convert a range of positions in a `ByteArray` into a `Nat`.
Assumes that each of those bytes has `isDigit`, otherwise the result is undefined. -/
def bytesToNat (buf : ByteArray) (s e : Nat) : Nat := Id.run do
  let mut ret : Nat := 0
  for i in [s:e] do
    ret := ret * 10 + (buf[i]!.val - 48)
  return ret

/-- Read a single byte without advancing the cursor.

This never fails: if EOI is encountered, `0` is returned.
Conversely, any null bytes in the actual file are treated like EOI. -/
@[inline] def readByte (buf : ByteArray) (pos : Nat) : UInt8 := Id.run do
  if h : pos < buf.size then
    return buf[pos]
  else
    return 0

/-- Return the first non-whitespace position that is at least `pos`. -/
@[inline] def consumeWhitespace (buf : ByteArray) (pos : Nat) : Nat := Id.run do
  let mut pos := pos
  let mut b := readByte buf pos
  while isWhitespace b do
    pos := pos + 1
    b := readByte buf pos
  return pos

/-- Like `consumeWhitespace`, but fail if `buf[pos]` isn't whitespace. -/
@[inline] def consumeWhitespacePlus (buf : ByteArray) (pos : Nat) : ParserM Nat :=
  let pos' := consumeWhitespace buf pos
  if pos' == pos then
    throw s!"expected whitespace, got '{Char.ofNat (readByte buf pos).val}' at {pos}"
  else
    return pos'

/-- Consume a positive natural number or a DIMACS `0`-terminator.
Return the number and the position right after it.
`0` is returned only on a terminator. -/
@[inline] def consumeNat (buf : ByteArray) (pos : Nat) : ParserM (Nat × Nat) := do
  let b := readByte buf pos
  if b == '0'.val.toUInt8 then
    return (0, pos+1)
  if !isDigit b then
    throw s!"expected positive natural number or 0-terminator, got '{Char.ofNat b.val}' at {pos}"
  let pStart := pos
  let mut pos := pos + 1
  let mut b := readByte buf pos
  while isDigit b do
    pos := pos + 1
    b := readByte buf pos
  let pEnd := pos
  return (bytesToNat buf pStart pEnd, pos)

@[inline] def consumePNat (buf : ByteArray) (pos : Nat) : ParserM (PNat × Nat) := do
  let (n, pos') ← consumeNat buf pos
  if h : 0 < n then
    return (⟨n, h⟩, pos')
  else
    throw s!"expected positive natural number, got 0 at {pos}"

/-- Consume a non-zero integer or a DIMACS `0`-terminator.
`0` is returned only on a terminator. -/
@[inline] def consumeInt (buf : ByteArray) (pos : Nat) : ParserM (Int × Nat) := do
  let b := readByte buf pos
  if b == '0'.val.toUInt8 then
    return (0, pos+1)
  if b == '-'.val.toUInt8 then
    let (n, pos') ← consumePNat buf (pos+1)
    return (-n.val, pos')
  if !isDigit b then
    throw s!"expected a digit or '-', got '{Char.ofNat b.val}' at {pos}"
  let (n, pos') ← consumePNat buf pos
  return (n.val, pos')

@[inline] def consumeILit (buf : ByteArray) (pos : Nat) : ParserM (ILit × Nat) := do
  let (i, pos') ← consumeInt buf pos
  if h : i ≠ 0 then
    return (⟨i, h⟩, pos')
  else throw s!"expected non-zero integer, got 0 at {pos}"

@[inline] def consumePNats (buf : ByteArray) (pos : Nat) : ParserM (Array PNat × Nat) := do
  let mut pos := pos
  let mut a := #[]
  let mut n := 0
  let (ni, posi) ← consumeNat buf pos
  n := ni
  pos := posi
  while h : 0 < n do
    a := a.push ⟨n, h⟩
    pos ← consumeWhitespacePlus buf pos
    let (ni, posi) ← consumeNat buf pos
    n := ni
    pos := posi
  return (a, pos)

-- TODO: ClauseIdx should be PNat
@[inline] unsafe def consumeNatsUnsafe (buf : ByteArray) (pos : Nat) : ParserM (Array Nat × Nat) :=
  return unsafeCast (← consumePNats buf pos)

@[implemented_by consumeNatsUnsafe, inline]
def consumeNats (buf : ByteArray) (pos : Nat) : ParserM (Array Nat × Nat) := do
  let (a, pos') ← consumePNats buf pos
  return (a.map (·.val), pos')

@[inline] def consumeILits (buf : ByteArray) (pos : Nat) : ParserM (Array ILit × Nat) := do
  let mut pos := pos
  let mut a := #[]
  let mut i := 0
  let (ii, posi) ← consumeInt buf pos
  i := ii
  pos := posi
  while h : i ≠ 0 do
    a := a.push ⟨i, h⟩
    pos ← consumeWhitespacePlus buf pos
    let (ii, posi) ← consumeInt buf pos
    i := ii
    pos := posi
  return (a, pos)

/-- Consume arbitrary characters until either a newline or EOI is seen. -/
def consumeComment (buf : ByteArray) (pos : Nat) : ParserM Nat := do
  let mut pos := pos
  let mut b := readByte buf pos
  while b != '\n'.val.toUInt8 && b != 0 do
    pos := pos + 1
    b := readByte buf pos
  return pos

/-- Consume an `a` step and return it. -/
def consumeAdd (buf : ByteArray) (pos : Nat) (idx : PNat) : ParserM (CpogStep × Nat) := do
  let (C, pos') ← consumeILits buf pos
  let pos'' ← consumeWhitespacePlus buf pos'
  let (hints, pos''') ← consumeNats buf pos''
  return (.addAt idx.val C hints, pos''')

/-- Consume a `d` step and return it. -/
def consumeDel (buf : ByteArray) (pos : Nat) : ParserM (CpogStep × Nat) := do
  let (idx, pos') ← consumePNat buf pos
  let pos'' ← consumeWhitespacePlus buf pos'
  let (hints, pos''') ← consumeNats buf pos''
  return (.delAt idx.val hints, pos''')

/-- Consume a `p` step and add it to the proof. -/
def consumeProd (buf : ByteArray) (pos : Nat) (idx : PNat) : ParserM (CpogStep × Nat) := do
  let (x, pos') ← consumePNat buf pos
  let pos'' ← consumeWhitespacePlus buf pos'
  let (ls, pos''') ← consumeILits buf pos''
  return (.prod idx.val x ls, pos''')

/-- Consume an `s` step and add it to the proof. -/
def consumeSum (buf : ByteArray) (pos : Nat) (idx : PNat) : ParserM (CpogStep × Nat) := do
  let (x, pos') ← consumePNat buf pos
  let pos'' ← consumeWhitespacePlus buf pos'
  let (l₁, pos''') ← consumeILit buf pos''
  let pos'''' ← consumeWhitespacePlus buf pos'''
  let (l₂, pos''''') ← consumeILit buf pos''''
  let pos'''''' ← consumeWhitespacePlus buf pos'''''
  let (hints, pos''''''') ← consumeNats buf pos'''''' -- lol
  return (.sum idx x l₁ l₂ hints, pos''''''')

/-- Consume an `r` step and add it to the proof. -/
def consumeRoot (buf : ByteArray) (pos : Nat) : ParserM (CpogStep × Nat) := do
  let (r, pos') ← consumeILit buf pos
  return (.root r, pos')

def consumeProof (buf : ByteArray) : ParserM (Array CpogStep) := do
  let mut pf := #[]
  let mut pos := 0
  let mut b := readByte buf pos
  while b != 0 /- while not EOI -/ do
    if b == 'c'.val.toUInt8 then
      pos := pos + 1
      pos ← consumeComment buf pos
    else if b == 'r'.val.toUInt8 then
      pos := pos + 1
      pos ← consumeWhitespacePlus buf pos
      let (s, pos') ← consumeRoot buf pos
      pf := pf.push s
      pos := pos'
    else if b == 'd'.val.toUInt8 then
      pos := pos + 1
      let b' := readByte buf pos
      -- Older CPOG format uses `dc`, newer uses `d`
      if b' == 'c'.val.toUInt8 then
        pos := pos + 1
      pos ← consumeWhitespacePlus buf pos
      let (s, pos') ← consumeDel buf pos
      pf := pf.push s
      pos := pos'
    else if isWhitespace b then
      pos := pos + 1
    else
      let (idx, pos') ← consumePNat buf pos
      pos ← consumeWhitespacePlus buf pos'
      let cmd := readByte buf pos
      pos ← consumeWhitespacePlus buf (pos+1)
      if cmd == 'a'.val.toUInt8 then
        let (s, pos') ← consumeAdd buf pos idx
        pf := pf.push s
        pos := pos'
      else if cmd == 'p'.val.toUInt8 then
        let (s, pos') ← consumeProd buf pos idx
        pf := pf.push s
        pos := pos'
      else if cmd == 's'.val.toUInt8 then
        let (s, pos') ← consumeSum buf pos idx
        pf := pf.push s
        pos := pos'
      else
        throw s!"expected a | d | p | s, got '{Char.ofNat b.val}'"
    b := readByte buf pos
  return pf

def CpogStep.readDimacsFileFast (fname : String) : IO (Array CpogStep) := do
  let buf ← IO.FS.readBinFile fname
  match consumeProof buf with
  | .ok pf => return pf
  | .error e => throw <| IO.userError s!"error: {e}"

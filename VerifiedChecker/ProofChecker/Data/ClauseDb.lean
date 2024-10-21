/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import LeanSAT.Data.ICnf
import LeanSAT.Data.PPA

import ProofChecker.Data.HashMap.Lemmas

/-! Clause database together with some (provably correct) methods. For example, we can conclude
that if a clause follows from the current database by unit propagation, then it is implied by the
database's interpretation as a propositional formula. -/

open LeanSAT Model

/-- A stateful clause database, i.e. a dynamically modifiable CNF,
for use in poly-time proof checkers such as for LRAT.
It uses in-place data structures, so should be used linearly.

(Persistent structures do not seem immediately helpful as linear formats do not backtrack.)

In `ClauseDb α`, `α` is the type of clause indices. -/
structure ClauseDb (α : Type) [BEq α] [Hashable α] where
  /-- Each clause is stored together with a flag indicating whether it has been deleted.
  Deleted clauses are logically not in the database. -/
  clauses : HashMap α (IClause × Bool) := {}

namespace HashMap

variable [BEq α] [Hashable α]

def mapOne (m : HashMap α β) (idx : α) (f : β → β) : HashMap α β :=
  match m.find? idx with
  | some b => m.insert idx (f b)
  | none => m

end HashMap

inductive UnitPropResult (α : Type) where
  | contradiction
  /-- The hint did not become unit. -/
  | hintNotUnit (hint : α)
  /-- The hint points at a nonexistent clause. -/
  | hintNonexistent (hint : α)
  | extended (τ : PartPropAssignment)

namespace UnitPropResult

def isContradiction (r : UnitPropResult α) : Bool :=
  r matches contradiction

end UnitPropResult

namespace ClauseDb

variable {α : Type} [BEq α] [Hashable α]

instance [ToString α] : ToString (ClauseDb α) where
  toString db := toString db.clauses.toList

def empty : ClauseDb α := { clauses := .empty }

def fold (db : ClauseDb α) (f : β → α → IClause → β) (init : β) : β :=
  db.clauses.fold (init := init) fun acc idx (C, deleted) =>
    if deleted then acc else f acc idx C

def foldM [Monad m] (db : ClauseDb α) (f : β → α → IClause → m β) (init : β) : m β :=
  db.clauses.foldM (init := init) fun acc idx (C, deleted) =>
    if deleted then pure acc else f acc idx C

def addClause (db : ClauseDb α) (idx : α) (C : IClause) : ClauseDb α :=
  { db with clauses := db.clauses.insert idx (C, false) }

def delClause (db : ClauseDb α) (idx : α) : ClauseDb α :=
  { db with clauses := db.clauses.mapOne idx fun (C, _) => (C, true) }

def getClause (db : ClauseDb α) (idx : α) : Option IClause :=
  db.clauses.find? idx |>.bind (fun (C, deleted) => if deleted then none else C)

def contains (db : ClauseDb α) (idx : α) : Bool :=
  db.getClause idx |>.isSome

/-- NOTE: This implementation is not efficient as it doesn't use early return. -/
def all (db : ClauseDb α) (p : α → IClause → Bool) : Bool :=
  db.fold (fun acc idx C => acc && p idx C) true

/-- NOTE: This implementation is not efficient as it doesn't use early return. -/
def any (db : ClauseDb α) (p : α → IClause → Bool) : Bool :=
  !db.all (fun idx C => !p idx C)

/-- Initialize a clause database from a CNF array. -/
def ofICnf (cnf : ICnf) : ClauseDb Nat :=
  let (db, _) := cnf.foldl (init := (empty, 1)) fun (db, idx) C =>
    (db.addClause idx C, idx + 1)
  db

/-! Theorems about `ClauseDb` -/

variable [LawfulBEq α] [HashMap.LawfulHashable α]

/-! `getClause` -/

theorem getClause_eq_some (db : ClauseDb α) (idx : α) (C : IClause) :
    db.getClause idx = some C ↔ db.clauses.find? idx = some (C, false) := by
  simp [getClause]

@[simp]
theorem getClause_empty (idx : α) : (empty : ClauseDb α).getClause idx = none := by
  simp [getClause, empty]

theorem getClause_addClause (db : ClauseDb α) (idx : α) (C : IClause) :
    (db.addClause idx C).getClause idx = some C := by
  dsimp [getClause, addClause]
  rw [HashMap.find?_insert _ _ (LawfulBEq.rfl)]
  simp

theorem getClause_addClause_of_ne (db : ClauseDb α) (idx idx' : α) (C : IClause) :
    idx ≠ idx' → (db.addClause idx C).getClause idx' = db.getClause idx' := by
  intro h
  dsimp [addClause, getClause]
  rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne idx idx' |>.mpr h)]

theorem getClause_delClause (db : ClauseDb α) (idx : α) :
    (db.delClause idx).getClause idx = none := by
  dsimp [getClause, delClause, HashMap.mapOne]
  split
  next =>
    rw [HashMap.find?_insert _ _ (LawfulBEq.rfl)]
    simp
  next h =>
    simp [h]

theorem getClause_delClause_of_ne (db : ClauseDb α) (idx idx' : α) :
    idx ≠ idx' → (db.delClause idx).getClause idx' = db.getClause idx' := by
  intro h
  dsimp [getClause, delClause, HashMap.mapOne]
  split
  next =>
    rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr h)]
  next => rfl

/-! `contains` -/

theorem contains_iff_getClause_eq_some (db : ClauseDb α) (idx : α) :
    db.contains idx ↔ ∃ C, db.getClause idx = some C := by
  simp [contains, Option.isSome_iff_exists, db.clauses.contains_iff]

@[simp]
theorem not_contains_empty (idx : α) : (empty : ClauseDb α).contains idx = false := by
  have := contains_iff_getClause_eq_some empty idx
  simp_all

theorem contains_addClause (db : ClauseDb α) (idx idx' : α) (C : IClause) :
    (db.addClause idx C).contains idx' ↔ (db.contains idx' ∨ idx = idx') := by
  simp only [contains_iff_getClause_eq_some]
  refine ⟨?mp, fun h => h.elim ?mpr₁ ?mpr₂⟩
  case mp =>
    intro ⟨C, hGet⟩
    by_cases hEq : idx = idx' <;>
      aesop (add norm getClause_addClause_of_ne)
  case mpr₁ =>
    intro ⟨C, hGet⟩
    by_cases hEq : idx = idx' <;>
      aesop (add norm getClause_addClause, norm getClause_addClause_of_ne)
  case mpr₂ =>
    aesop (add norm getClause_addClause)

theorem contains_delClause (db : ClauseDb α) (idx idx' : α) :
    (db.delClause idx).contains idx' ↔ (db.contains idx' ∧ idx ≠ idx') := by
  simp only [contains_iff_getClause_eq_some]
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro ⟨C, hGet⟩
    have hEq : idx ≠ idx' := fun h => by
      rw [h, getClause_delClause] at hGet
      cases hGet
    rw [getClause_delClause_of_ne _ _ _ hEq] at hGet
    simp [hGet, hEq]
  case mpr =>
    intro ⟨⟨C, hGet⟩, hEq⟩
    exact ⟨C, hGet ▸ getClause_delClause_of_ne _ _ _ hEq⟩

/-! `fold` -/

theorem fold_of_getClause_eq_some_of_comm (db : ClauseDb α) (idx : α) (C : IClause)
    (f : β → α → IClause → β) (init : β) :
    db.getClause idx = some C →
    (∀ b a₁ C₁ a₂ C₂, f (f b a₁ C₁) a₂ C₂ = f (f b a₂ C₂) a₁ C₁) →
    ∃ b, db.fold f init = f b idx C := by
  intro h hComm
  rw [getClause_eq_some] at h
  have ⟨b, hb⟩ := db.clauses.fold_of_mapsTo_of_comm (init := init)
    (f := fun acc idx (C, deleted) => if deleted then acc else f acc idx C)
    h (by aesop)
  use b
  simp [fold, hb]

/-! `all` -/

theorem all_true (db : ClauseDb α) (p : α → IClause → Bool) :
    db.all p → ∀ idx C, db.getClause idx = some C → p idx C := by
  dsimp [all]
  intro hAll idx C hGet
  have ⟨b, hEq⟩ :=
    fold_of_getClause_eq_some_of_comm db idx C (fun acc idx C => acc && p idx C) true
      hGet ?comm
  case comm =>
    intros
    simp only [Bool.and_assoc]
    rw [Bool.and_comm (p _ _)]
  simp_all

theorem all_of_all_true (db : ClauseDb α) (p : α → IClause → Bool) :
    (∀ idx C, db.getClause idx = some C → p idx C) → db.all p := by
  dsimp [all, fold, getClause]
  intro
  apply db.clauses.foldRecOn (C := fun b => b = true) (hInit := rfl)
  simp_all

/-! `any` -/

theorem any_true (db : ClauseDb α) (p : α → IClause → Bool) :
    db.any p → ∃ idx C, db.getClause idx = some C ∧ p idx C = true := by
  have := db.all_of_all_true (fun idx C => !p idx C)
  dsimp [any]
  exact not_imp_not.mp fun _ => by simp_all

/-! `toPropFunSub` -/

open Classical PropFun

/-- Interpret the conjunction of a subset of the clauses as a Boolean function. -/
noncomputable def toPropFunSub (db : ClauseDb α) (idxs : Set α) : PropFun IVar :=
  db.fold (init := ⊤) fun acc idx C => if idx ∈ idxs then acc ⊓ C.toPropFun else acc

theorem toPropFunSub_of_getClause_eq_some (db : ClauseDb α) :
    idx ∈ idxs → db.getClause idx = some C → db.toPropFunSub idxs ≤ C.toPropFun := by
  intro hMem hGet
  have ⟨φ, hφ⟩ := db.fold_of_getClause_eq_some_of_comm idx C
    (init := ⊤) (f := fun acc idx C => if idx ∈ idxs then acc ⊓ C.toPropFun else acc)
    hGet ?comm
  case comm =>
    intros
    dsimp
    split_ifs <;> ac_rfl
  apply PropFun.entails_ext.mpr
  rw [toPropFunSub, hφ]
  simp [hMem]

theorem satisfies_toPropFunSub (db : ClauseDb α) (idxs : Set α) (σ : PropAssignment IVar) :
    σ ⊨ db.toPropFunSub idxs ↔ ∀ idx ∈ idxs, ∀ C, db.getClause idx = some C → σ ⊨ C.toPropFun :=
  ⟨mp, mpr⟩
where
  mp := fun h idx hMem C hGet =>
    entails_ext.mp (toPropFunSub_of_getClause_eq_some db hMem hGet) _ h

  mpr := fun h => by
    dsimp [toPropFunSub]
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ idx (C, deleted) hφ hFind
    dsimp
    split_ifs <;> try assumption
    next hDel hMem =>
      rw [satisfies_conj]
      refine ⟨by assumption, ?_⟩
      apply h idx hMem
      simp [getClause, hFind, hDel]

@[simp]
theorem toPropFunSub_empty (idxs : Set α) : (empty : ClauseDb α).toPropFunSub idxs = ⊤ := by
  ext τ
  simp [satisfies_toPropFunSub]

@[simp]
theorem toPropFunSub_emptySet (db : ClauseDb α) : db.toPropFunSub ∅ = ⊤ := by
  ext τ
  aesop (add norm satisfies_toPropFunSub)

theorem toPropFunSub_subset (db : ClauseDb α) :
    idxs ⊆ idxs' → db.toPropFunSub idxs' ≤ db.toPropFunSub idxs := by
  intro hSub
  apply entails_ext.mpr
  aesop (add norm satisfies_toPropFunSub)

theorem toPropFunSub_subset_eq (db : ClauseDb α) :
    idxs ⊆ idxs' → (∀ idx ∈ idxs', db.contains idx → idx ∈ idxs) →
    db.toPropFunSub idxs' = db.toPropFunSub idxs := by
  intro hSub h
  apply le_antisymm (toPropFunSub_subset db hSub)
  apply entails_ext.mpr
  simp only [satisfies_toPropFunSub]
  intro τ hτ _ hMem' _ hGet'
  exact hτ _ (h _ hMem' (contains_iff_getClause_eq_some _ _ |>.mpr ⟨_, hGet'⟩)) _ hGet'

theorem toPropFunSub_addClause (db : ClauseDb α) (idxs : Set α) (idx : α) (C : IClause) :
    db.toPropFunSub idxs ⊓ C.toPropFun ≤ (db.addClause idx C).toPropFunSub idxs := by
  apply entails_ext.mpr
  simp only [satisfies_conj, satisfies_toPropFunSub]
  intro τ h idx' C' hMem' hGet'
  by_cases hEq : idx = idx' <;>
    aesop (add norm getClause_addClause, norm getClause_addClause_of_ne)

theorem toPropFunSub_addClause_of_not_contains (db : ClauseDb α) (C : IClause) :
    ¬db.contains idx → (db.addClause idx C).toPropFunSub idxs ≤ db.toPropFunSub idxs := by
  intro hContains
  apply entails_ext.mpr
  simp only [satisfies_toPropFunSub]
  intro _ _ idx'
  by_cases hEq : idx = idx' <;>
    aesop (add norm contains_iff_getClause_eq_some, norm getClause_addClause_of_ne)

theorem toPropFunSub_addClause_eq (db : ClauseDb α) (C : IClause) :
    idx ∈ idxs → ¬db.contains idx →
    (db.addClause idx C).toPropFunSub idxs = db.toPropFunSub idxs ⊓ C.toPropFun := by
  intro hMem hContains
  refine le_antisymm ?_ (toPropFunSub_addClause db idxs idx C)
  apply le_inf (toPropFunSub_addClause_of_not_contains db C hContains)
  apply toPropFunSub_of_getClause_eq_some _ hMem
  apply getClause_addClause

theorem toPropFunSub_addClause_of_not_mem (db : ClauseDb α) (C : IClause) :
    idx ∉ idxs → (db.addClause idx C).toPropFunSub idxs = db.toPropFunSub idxs := by
  intro hMem
  ext τ
  simp only [satisfies_toPropFunSub]
  constructor <;> {
    intro h idx' hMem'
    have : idx ≠ idx' := fun h =>
      hMem <| h ▸ hMem'
    aesop (add norm getClause_addClause_of_ne)
  }

theorem toPropFunSub_delClause (db : ClauseDb α) (idxs : Set α) (idx : α) :
    db.toPropFunSub idxs ≤ (db.delClause idx).toPropFunSub idxs := by
  apply PropFun.entails_ext.mpr
  simp only [satisfies_toPropFunSub]
  intro _ _ idx'
  by_cases hEq : idx = idx' <;>
    aesop (add norm getClause_delClause_of_ne, norm getClause_delClause)

theorem toPropFunSub_delClause_of_getClause_eq_some (db : ClauseDb α) :
    db.getClause idx = some C →
    (db.delClause idx).toPropFunSub idxs ⊓ C.toPropFun ≤ db.toPropFunSub idxs := by
  intro hGet
  apply entails_ext.mpr
  simp only [satisfies_conj, satisfies_toPropFunSub]
  intro _ _ idx'
  by_cases hEq : idx = idx' <;>
    aesop (add norm getClause_delClause_of_ne)

theorem toPropFunSub_delClause_eq (db : ClauseDb α) :
    idx ∈ idxs → db.getClause idx = some C →
    (db.delClause idx).toPropFunSub idxs ⊓ C.toPropFun = db.toPropFunSub idxs := by
  intro hMem hGet
  apply le_antisymm (toPropFunSub_delClause_of_getClause_eq_some db hGet)
  apply le_inf (toPropFunSub_delClause db idxs idx)
  apply toPropFunSub_of_getClause_eq_some _ hMem hGet

theorem toPropFunSub_delClause_of_not_mem (db : ClauseDb α) :
    idx ∉ idxs → (db.delClause idx).toPropFunSub idxs = db.toPropFunSub idxs := by
  intro hMem
  ext τ
  simp only [satisfies_toPropFunSub]
  constructor <;> {
    intro h idx' hMem'
    have : idx ≠ idx' := fun h =>
      hMem <| h ▸ hMem'
    aesop (add norm getClause_delClause_of_ne)
  }

/-! `toPropFun` -/

/-- Interpret the conjuction of all the clauses as a Boolean function. -/
noncomputable def toPropFun (db : ClauseDb α) : PropFun IVar :=
  db.toPropFunSub Set.univ

theorem toPropFun_of_getClause_eq_some (db : ClauseDb α) :
    db.getClause idx = some C → db.toPropFun ≤ C.toPropFun :=
  toPropFunSub_of_getClause_eq_some db (Set.mem_univ idx)

open PropFun in
theorem satisfies_toPropFun (db : ClauseDb α) (σ : PropAssignment IVar) :
    σ ⊨ db.toPropFun ↔ ∀ idx C, db.getClause idx = some C → σ ⊨ C.toPropFun :=
  have ⟨mp, mpr⟩ := satisfies_toPropFunSub db Set.univ σ
  ⟨fun h idx C hGet => mp h idx (Set.mem_univ idx) C hGet,
   fun h => mpr (fun idx _ C hGet => h idx C hGet)⟩

theorem toPropFun_subset (db : ClauseDb α) (idxs : Set α) :
    db.toPropFun ≤ db.toPropFunSub idxs :=
  toPropFunSub_subset db (Set.subset_univ idxs)

@[simp]
theorem toPropFun_empty : (empty : ClauseDb α).toPropFun = ⊤ :=
  toPropFunSub_empty Set.univ

theorem toPropFun_addClause (db : ClauseDb α) (idx : α) (C : IClause) :
    db.toPropFun ⊓ C.toPropFun ≤ (db.addClause idx C).toPropFun :=
  toPropFunSub_addClause db Set.univ idx C

theorem toPropFun_addClause_eq (db : ClauseDb α) (idx : α) (C : IClause) :
    ¬db.contains idx →
    (db.addClause idx C).toPropFun = db.toPropFun ⊓ C.toPropFun :=
  toPropFunSub_addClause_eq db C (Set.mem_univ idx)

theorem toPropFun_delClause (db : ClauseDb α) (idx : α) :
    db.toPropFun ≤ (db.delClause idx).toPropFun :=
  toPropFunSub_delClause db Set.univ idx

theorem toPropFun_delClause_eq (db : ClauseDb α) (idx : α) (C : IClause) :
    db.getClause idx = some C →
    (db.delClause idx).toPropFun ⊓ C.toPropFun = db.toPropFun :=
  toPropFunSub_delClause_eq db (Set.mem_univ idx)

/-! `ofICnf` -/

theorem ofICnf_characterization (cnf : ICnf) :
    ¬(ofICnf cnf).contains 0 ∧
    (∀ i : Fin cnf.size, (ofICnf cnf).getClause (i + 1) = some cnf[i]) ∧
    (∀ i > cnf.size, ¬(ofICnf cnf).contains i) := by
  have ⟨h₁, h₂, h₃, _⟩ := cnf.foldl_induction
    (motive := fun (sz : Nat) (p : ClauseDb Nat × Nat) =>
      ¬p.1.contains 0 ∧
      (∀ i : Fin cnf.size, i < sz → p.1.getClause (i + 1) = some cnf[i]) ∧
      (∀ i > sz, ¬p.1.contains i) ∧
      p.2 = sz + 1)
    (init := (empty, 1))
    (f := fun (db, idx) C => (db.addClause idx C, idx + 1))
    (h0 := by simp [not_contains_empty])
    (hf := by
      intro sz (db, idx) ⟨ih₁, ih₂, ih₃, ih₄⟩
      dsimp at ih₄ ⊢
      simp only [ih₄, contains_iff_getClause_eq_some, and_true] at *
      refine ⟨?step₁, ?step₂, ?step₃⟩
      case step₁ =>
        have : sz.val + 1 ≠ 0 := Nat.succ_ne_zero _
        simp [getClause_addClause_of_ne _ _ _ _ this, ih₁]
      case step₂ =>
        intro i hLt
        by_cases hEq : sz.val = i.val
        . simp [hEq, getClause_addClause]
        . have : sz.val + 1 ≠ i.val + 1 := by simp [hEq]
          rw [getClause_addClause_of_ne _ _ _ _ this]
          apply ih₂
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hLt) (Ne.symm hEq)
      case step₃ =>
        intro i hGe
        have : sz.val + 1 ≠ i := Nat.ne_of_lt hGe
        rw [getClause_addClause_of_ne _ _ _ _ this]
        apply ih₃
        linarith)
  dsimp [ofICnf]
  exact ⟨h₁, fun i => h₂ i i.isLt, h₃⟩

theorem ofICnf_ext (cnf : ICnf) (C : IClause) :
    C ∈ cnf.data ↔ ∃ idx, (ofICnf cnf).getClause idx = some C := by
  have ⟨h₁, h₂, h₃⟩ := ofICnf_characterization cnf
  apply Iff.intro
  case mp =>
    intro h
    have ⟨i, h⟩ := Array.get_of_mem_data h
    use (i + 1)
    rw [← h]
    apply h₂
  case mpr =>
    intro ⟨idx, h⟩
    have hContains := contains_iff_getClause_eq_some _ _ |>.mpr ⟨C, h⟩
    have hPos : 0 < idx := by
      apply Nat.pos_of_ne_zero
      intro
      simp_all
    have hLt : idx - 1 < cnf.size := by
      suffices idx ≤ cnf.size by
        apply Nat.sub_lt_left_of_lt_add
        . apply Nat.succ_le_of_lt hPos
        . rw [add_comm]
          apply Nat.lt_succ_of_le this
      by_contra
      simp_all
    have hPred : idx - 1 + 1 = idx := Nat.succ_pred_eq_of_pos hPos
    have := h₂ ⟨idx - 1, hLt⟩
    simp only [hPred, h] at this
    cases this
    apply Array.get_mem_data

@[simp]
theorem toPropFun_ofICnf (cnf : ICnf) : (ofICnf cnf).toPropFun = cnf.toPropFun := by
  ext τ
  simp only [Cnf.satisfies_iff, satisfies_toPropFun, ofICnf_ext]
  aesop

/-! `unitPropWithHints` -/

inductive UPResult {α : Type} [BEq α] [Hashable α]
    (db : ClauseDb α) (C : IClause) (hints : Array α) where
  /-- A contradiction was derived. The contradiction is implied by the subset of the database
  used in hints as well as the initial assignment. -/
  | contradiction (h : db.toPropFunSub (· ∈ hints.data) ⊓ C.toPropFunᶜ ≤ ⊥)
  /-- The partial assignment was extended. The final assignment `σ'` is implied by the subset of
  the database used in hints as well as the initial assignment. -/
  | extended --(h : db.toPropFunSub (· ∈ hints.data) ⊓ C.toPropFunᶜ ≤ τ.toPropFun) if τ : PPA is returned
  /-- The hint `C` at index `idx` did not become unit under `σ`. -/
  | hintNotUnit (idx : α) (C : IClause) --(σ : PartPropAssignment)
  /-- The hint index `idx` points at a nonexistent clause. -/
  | hintNonexistent (idx : α)

/-- Propagate units starting from `¬C`.
The clauses in `hints` are expected to become unit
in the order provided. -/
def propagateUnitsHinted (db : ClauseDb α) (τ : PPA) (C : IClause) (hints : Array α)
    : PPA × UPResult db C hints :=
  go 0 ⟨τ.reset.setNegatedClause C, inf_le_of_right_le (τ.toPropFun_reset_setNegatedClause _)⟩
where go (i : Nat) (τ : {τ : PPA // db.toPropFunSub (· ∈ hints.data) ⊓ (C.toPropFun)ᶜ ≤ τ.toPropFun}) :=
  if h : i < hints.size then
    let hint := hints[i]'h
    have hMem : hint ∈ hints.data := Array.getElem_mem_data hints _
    match hGet : db.getClause hint with
    | none => (τ, .hintNonexistent hint)
    | some hintC =>
      let ⟨τ', res⟩ := τ.val.propagateUnit hintC
      match hRes : res with
      | .contradiction h =>
        (τ', .contradiction (by
          rw [← h]
          refine le_inf ?_ τ.property
          apply inf_le_of_left_le
          exact db.toPropFunSub_of_getClause_eq_some hMem hGet))
      | .extended l _ h₁ h₂ =>
        go (i+1) ⟨τ', by
          rw [h₁]
          refine le_inf ?_ τ.property
          refine le_trans ?_ h₂
          apply le_inf τ.property
          apply inf_le_of_left_le
          exact db.toPropFunSub_of_getClause_eq_some hMem hGet⟩
      | .satisfied => (τ', .hintNotUnit hint hintC)
      | .notUnit => (τ', .hintNotUnit hint hintC)
  else
    (τ.val, .extended)
  termination_by go i _ => hints.size - i

/-- This has the same functionality as `propagateUnitsHinted`,
but the use of `do` notation unfortunately macro-expands into code
that does not use the PPA linearly,
so this variant is exceedingly inefficient.
Thus we had to hand-rool the propagation loop. -/
def propagateUnitsHinted' (db : ClauseDb α) (τ : PPA) (C : IClause) (hints : Array α)
    : PPA × UPResult db C hints := Id.run do
  let mut τ : {τ : PPA // db.toPropFunSub (· ∈ hints.data) ⊓ (C.toPropFun)ᶜ ≤ τ.toPropFun } :=
    ⟨τ.reset.setNegatedClause C, inf_le_of_right_le (τ.toPropFun_reset_setNegatedClause _)⟩
  for h : i in [0:hints.size] do
    let hint := hints[i]'(Membership.mem.upper h)
    have hMem : hint ∈ hints.data := Array.getElem_mem_data hints _
    match hGet : db.getClause hint with
    | none => return (τ, .hintNonexistent hint)
    | some hintC =>
      let ⟨τ', res⟩ := τ.val.propagateUnit hintC
      match hRes : res with
      | .contradiction h =>
        return (τ', .contradiction (by
          rw [← h]
          refine le_inf ?_ τ.property
          apply inf_le_of_left_le
          exact db.toPropFunSub_of_getClause_eq_some hMem hGet))
      | .extended l _ h₁ h₂ =>
        τ := ⟨τ', by
          rw [h₁]
          refine le_inf ?_ τ.property
          refine le_trans ?_ h₂
          apply le_inf τ.property
          apply inf_le_of_left_le
          exact db.toPropFunSub_of_getClause_eq_some hMem hGet⟩
      | .satisfied => return (τ', .hintNotUnit hint hintC)
      | .notUnit => return (τ', .hintNotUnit hint hintC)
  return (τ, .extended)

end ClauseDb

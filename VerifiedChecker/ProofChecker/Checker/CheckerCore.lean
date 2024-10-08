/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Data.Array.Basic
import Std.Data.RBMap

import ProofChecker.Data.ClauseDb
import ProofChecker.Data.Pog
import ProofChecker.Count.Pog
import ProofChecker.Data.HashSet
import ProofChecker.Data.RBSet
import ProofChecker.Model.Cpog

/-- An index into the `ClauseDb`. -/
abbrev ClauseIdx := Nat

open LeanSAT Model

open Std (RBSet)

/-- A step in a CPOG proof. -/
inductive CpogStep
  | /-- Add asymmetric tautology. -/
    addAt (idx : ClauseIdx) (C : IClause) (upHints : Array ClauseIdx)
  | /-- Delete asymmetric tautology. -/
    delAt (idx : ClauseIdx) (upHints : Array ClauseIdx)
  | /-- Declare product operation. -/
    prod (idx : ClauseIdx) (x : Var) (ls : Array ILit)
  | /-- Declare sum operation. -/
    sum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (upHints : Array ClauseIdx)
  | /-- Declare POG root. -/
    root (r : ILit)

namespace CpogStep

def toDimacs : CpogStep → String
  | addAt idx C upHints => s!"{idx} a {pArray C} 0 {pArray upHints} 0"
  | delAt idx upHints => s!"d {idx} {pArray upHints} 0"
  | prod idx x ls => s!"{idx} p {x} {pArray ls} 0"
  | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} {pArray upHints} 0"
  | root x => s!"r {x}"
where
  pArray {α : Type} [ToString α] (a : Array α) :=
    " ".intercalate (a.foldr (init := []) fun a acc => toString a :: acc)

instance : ToString CpogStep where
  toString := fun
    | addAt idx C upHints => s!"{idx} a {C} 0 (hints: {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x ls => s!"{idx} p {x} {ls}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | root x => s!"r {x}"

end CpogStep

inductive CheckerError where
  | graphUpdateError (err : PogError)
  | duplicateClauseIdx (idx : ClauseIdx)
  | unknownClauseIdx (idx : ClauseIdx)
  | pogDefClause (idx : ClauseIdx)
  | hintNotPog (idx : ClauseIdx)
  | hintNotUnit (idx : ClauseIdx) (C : IClause) --(σ : PartPropAssignment)
  | upNoContradiction -- (τ : PartPropAssignment)
  | duplicateExtVar (x : Var)
  | unknownVar (x : Var)
  | depsNotDisjoint (xs : List Var)
  | finalRootNotSet
  | finalRootNotUnit (r : ILit)
  | finalClausesInvalid
  | finalClauseInvalid (idx : ClauseIdx) (C : IClause)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"cannot add clause at index {idx}, index is already used"
    | unknownClauseIdx idx => s!"there is no clause at index {idx}"
    | pogDefClause idx => s!"clause at index {idx} cannot be deleted because it is a POG definition"
    | hintNotPog idx => s!"hint {idx} cannot be used to imply model disjointness because it's not
    a POG definition clause"
    | hintNotUnit idx C =>
      s!"hinted clause {C} at index {idx} did not become unit under assignment (TBD)"
    | upNoContradiction =>
      s!"unit propagation did not derive contradiction (final assignment (TBD))"
    | duplicateExtVar x => s!"extension variable {x} was already introduced"
    | unknownVar x => s!"unknown variable {x}"
    | depsNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalRootNotSet => s!"proof done but root literal was not set"
    | finalRootNotUnit r => s!"proof done but root literal {r} was not asserted as a unit clause"
    | finalClausesInvalid =>
      s!"proof done but some clause is neither the asserted root nor a POG definition"
    | finalClauseInvalid idx C =>
      s!"proof done but clause {C} at index {idx} is neither the asserted root nor a POG definition"

end CheckerError

/-- The checker's runtime state. Contains exactly the data needed to fully check a proof.
It can be ill-formed, so it's a "pre"-well-formed state. -/
structure PreState where
  -- NOTE: This is part of the state so we could cheat by changing it. We don't.
  inputCnf : ICnf

  /-- The clause database. -/
  clauseDb : ClauseDb ClauseIdx

  up : PPA

  /-- Which clauses are POG definition clauses. -/
  pogDefs : HashSet ClauseIdx

  /-- The partitioned-operation graph. -/
  pog : Pog

  /-- Maps any variable present in `pog` to the set of all *original* variables it depends on.
  For example, an original `x` is mapped to `{x}` whereas an extension `p` with `p ↔ x ∧ y` is
  mapped to `{x, y}`.

  Variables not present in `pog` are not present in this map. Thus we maintain the invariant
  that a variable is in the `pog` iff it is in the domain of this map. -/
  depVars : HashMap Var (RBSet Var compare)

  /-- The POG root literal, if we already saw a `root` instruction. Otherwise `none`. -/
  root : Option ILit

def PreState.pogDefs' (st : PreState) : Finset ClauseIdx :=
  st.pogDefs.toFinset

noncomputable def PreState.pogDefsTerm (st : PreState) : PropFun Var :=
  st.clauseDb.toPropFunSub st.pogDefs'

def PreState.allVars (st : PreState) : Set Var :=
  { x | st.depVars.contains x }

open PropFun

structure PreState.WF (st : PreState) : Prop where
  /-- The POG definition clauses are all in the clause database. -/
  pogDefs_in_clauseDb : ∀ idx : ClauseIdx, idx ∈ st.pogDefs' → st.clauseDb.contains idx

  /-- Variable dependencies are correctly stored in `depVars`. -/
  depVars_pog : ∀ (x : Var) (D : RBSet Var compare), st.depVars.find? x = some D →
    -- NOTE: can strengthen to iff if needed
    ∀ y ∈ (st.pog.toPropForm x).vars, y ∈ D

  /-- Every formula in the POG forest is partitioned.

  For literals not defining anything in the forest this still holds by fiat because
  `st.pog.toPropForm l = l.toPropForm`. -/
  partitioned : ∀ x : Var, partitioned (st.pog.toPropForm x)

  /-- `depVars` contains all variables that influence the clause database. Contrapositive:
  if a variable is not in `depVars` then it does not influence the clause database so can be
  defined as an extension variable. -/
  clauseDb_semVars_sub : ↑st.clauseDb.toPropFun.semVars ⊆ st.allVars

  pogDefsTerm_semVars_sub : ↑st.pogDefsTerm.semVars ⊆ st.allVars

  inputCnf_vars_sub : ↑st.inputCnf.toPropForm.vars ⊆ st.allVars

  /-- Every formula in the POG forest lives over the original variables. -/
  pog_vars : ∀ x : Var, x ∈ st.allVars →
    (st.pog.toPropForm x).vars ⊆ st.inputCnf.toPropForm.vars

  /-- The clause database is equivalent to the original formula over original variables. -/
  equivalent_clauseDb : equivalentOver st.inputCnf.toPropForm.vars
    st.inputCnf.toPropFun st.clauseDb.toPropFun

  extends_pogDefsTerm : ∀ (σ₁ : PropAssignment Var), ∃ (σ₂ : PropAssignment Var),
    σ₂.agreeOn st.inputCnf.toPropForm.vars σ₁ ∧ σ₂ ⊨ st.pogDefsTerm

  /-- The POG definition clauses extend uniquely from the original variables to the current set
  of variables. -/
  uep_pogDefsTerm : hasUniqueExtension st.inputCnf.toPropForm.vars st.allVars
    st.pogDefsTerm

  /-- In the context of the POG defining clauses, every variable is s-equivalent over original
  variables to what it defines in the POG forest. -/
  -- TODO: could this be weakened to `extendsOver` and still go through?
  equivalent_lits : ∀ x : Var, equivalentOver st.inputCnf.toPropForm.vars
    (.var x ⊓ st.pogDefsTerm) ⟦st.pog.toPropForm x⟧

theorem PreState.WF.depVars_pog' {st : PreState} (hWf : st.WF) (l : ILit) (D : RBSet Var compare) :
    st.depVars.find? l.var = some D → ∀ y ∈ (st.pog.toPropForm l).vars, y ∈ D :=
  fun hFind => l.mkPos_or_mkNeg.elim (· ▸ hWf.depVars_pog l.var D hFind) fun h => by
   rw [h, Pog.toPropForm_neg, PropForm.vars]
   exact hWf.depVars_pog l.var D hFind

theorem PreState.WF.partitioned' {st : PreState} (hWf : st.WF) (l : ILit) :
    _root_.partitioned (st.pog.toPropForm l) :=
  l.mkPos_or_mkNeg.elim (· ▸ hWf.partitioned l.var) fun h => by
    rw [h, Pog.toPropForm_neg]
    exact hWf.partitioned l.var

theorem PreState.WF.pog_vars' {st : PreState} (hWf : st.WF) (l : ILit) :
    l.var ∈ st.allVars → (st.pog.toPropForm l).vars ⊆ st.inputCnf.toPropForm.vars :=
  fun hMem => l.mkPos_or_mkNeg.elim (· ▸ hWf.pog_vars l.var hMem) fun h => by
    rw [h, Pog.toPropForm_neg]
    exact hWf.pog_vars l.var hMem

theorem PreState.WF.pog_semVars {st : PreState} (hWf : st.WF) (l : ILit) :
    l.var ∈ st.allVars → ↑(PropFun.semVars ⟦st.pog.toPropForm l⟧) ⊆ st.inputCnf.toPropForm.vars :=
  fun hMem => subset_trans (PropForm.semVars_subset_vars _) (hWf.pog_vars' l hMem)

theorem PreState.WF.equivalent_lits' {st : PreState} (hWf : st.WF) (l : ILit) :
    LitVar.toVar l ∈ st.allVars → equivalentOver st.inputCnf.toPropForm.vars
      (LitVar.toPropFun l ⊓ st.pogDefsTerm) ⟦st.pog.toPropForm l⟧ := by
  intro hMem
  cases l.mkPos_or_mkNeg
  next hMk =>
    rw [hMk]
    simp [hWf.equivalent_lits l.var]
  next hMk =>
    rw [hMk]
    generalize LitVar.toVar l = x at hMem ⊢
    have hEquiv := hWf.equivalent_lits x
    simp only [Pog.toPropForm_neg, LitVar.toPropFun_mkNeg, PropFun.mk_neg]
    apply equivalentOver_iff_extendsOver _ _ _ |>.mpr
    constructor
    . intro σ hσ
      refine ⟨σ, PropAssignment.agreeOn_refl _ _, ?_⟩
      rw [satisfies_neg]
      intro h
      have ⟨σ₂, hAgree, hσ₂⟩ := hEquiv σ |>.mpr ⟨σ, PropAssignment.agreeOn_refl _ _, h⟩
      have hAgree := hWf.uep_pogDefsTerm (satisfies_conj.mp hσ₂).right (satisfies_conj.mp hσ).right hAgree
      have : σ₂.agreeOn (PropFun.var x).semVars σ := hAgree.subset (by simp [hMem])
      have : σ ⊨ .var x := agreeOn_semVars this |>.mp (satisfies_conj.mp hσ₂).left
      have : σ ⊭ .var x := satisfies_neg.mp (satisfies_conj.mp hσ).left
      contradiction
    . intro σ hσ
      have ⟨σ₁, hAgree, hσ₁⟩ := hWf.extends_pogDefsTerm σ
      refine ⟨σ₁, hAgree, ?_⟩
      simp only [hσ₁, satisfies_conj, satisfies_neg, and_true]
      intro h
      have ⟨σ₂, hAgree₂, hσ₂⟩ := hEquiv σ₁ |>.mp
        ⟨σ₁, PropAssignment.agreeOn_refl _ _, satisfies_conj.mpr ⟨h, hσ₁⟩⟩
      have hAgree := hAgree₂.trans hAgree
      have hSub := hWf.pog_semVars (.mkPos x) hMem
      have : σ ⊨ ⟦st.pog.toPropForm (.mkPos x)⟧ :=
        agreeOn_semVars (hAgree.subset hSub) |>.mp hσ₂
      simp [satisfies_neg] at hσ
      contradiction

/-- A well-formed checker state. -/
def State := { st : PreState // st.WF }

abbrev CheckerM := StateT State <| Except CheckerError

def initialPog (nVars : Nat) :
    Except CheckerError { p : Pog // ∀ l, p.toPropForm l = l.toPropForm } := do
  -- NOTE: We add all input variables to the POG in-order because that's what the current
  -- implementation expects, but this requirement is artificial. See `Pog.lean`.
  nVars.foldM (init := ⟨Pog.empty, Pog.toPropForm_empty⟩) fun x ⟨acc, hAcc⟩ =>
    let x := ⟨x + 1, Nat.zero_lt_succ _⟩
    match h : acc.addVar x with
    | .ok g => pure ⟨g, by
      intro l'
      by_cases hEq : x = l'.var
      . rw [hEq] at h
        exact acc.toPropForm_addVar_lit _ _ h
      . rw [acc.toPropForm_addVar_lit_of_ne _ _ _ h hEq]
        apply hAcc⟩
    | .error e => throw <| .graphUpdateError e

def initialClauseVars (m : HashMap Var (RBSet Var compare)) (C : IClause) : HashMap Var (RBSet Var compare) :=
  C.foldl (init := m) fun m l =>
    m.insert l.var (.empty |>.insert l.var)

theorem initialClauseVars₁ (m : HashMap Var (RBSet Var compare)) (C : IClause) (x : Var) :
    (initialClauseVars m C).contains x ↔ x ∈ C.toPropForm.vars ∨ m.contains x := by
  simp only [initialClauseVars, Clause.mem_vars, Array.foldl_eq_foldl_data]
  induction C.data generalizing m <;>
    aesop (add norm HashMap.contains_insert)

theorem initialClauseVars₂ (m : HashMap Var (RBSet Var compare)) (C : IClause) :
    (∀ x D, m.find? x = some D → x ∈ D) →
    ∀ x D, (initialClauseVars m C).find? x = some D → x ∈ D := by
  simp only [initialClauseVars, Array.foldl_eq_foldl_data]
  induction C.data generalizing m
  . simp
  next l _ ih =>
    intro _ _ _
    rw [List.foldl_cons]
    apply ih
    intro y
    by_cases hEq : l.var = y <;>
      aesop (add norm HashMap.find?_insert, safe RBSet.mem_insert_self, norm HashMap.find?_insert_of_ne)

def initialCnfVars (m : HashMap Var (RBSet Var compare)) (φ : ICnf) : HashMap Var (RBSet Var compare) :=
  φ.foldl (init := m) initialClauseVars

theorem initialCnfVars₁ (m : HashMap Var (RBSet Var compare)) (φ : ICnf) (x : Var) :
    (initialCnfVars m φ).contains x ↔ x ∈ φ.toPropForm.vars ∨ m.contains x := by
  simp only [initialCnfVars, Array.foldl_eq_foldl_data]
  rw [Cnf.mem_vars]
  induction φ.data generalizing m <;> aesop (add norm initialClauseVars₁)

theorem initialCnfVars₂ (m : HashMap Var (RBSet Var compare)) (φ : ICnf) :
    (∀ x D, m.find? x = some D → x ∈ D) →
    ∀ x D, (initialCnfVars m φ).find? x = some D → x ∈ D := by
  simp only [initialCnfVars, Array.foldl_eq_foldl_data]
  induction φ.data generalizing m
  . simp
  next C _ ih =>
    intro h _ _
    rw [List.foldl_cons]
    apply ih
    exact initialClauseVars₂ _ _ h

def initialDepVars (inputCnf : ICnf) : { dv : HashMap Var (RBSet Var compare) //
    { y | dv.contains y } = inputCnf.toPropForm.vars ∧
    ∀ x D, dv.find? x = some D → x ∈ D } :=
  let dv := initialCnfVars .empty inputCnf
  have allVars_eq := by ext; simp [initialCnfVars₁]
  have of_find := by apply initialCnfVars₂; simp
  ⟨dv, allVars_eq, of_find⟩

def initial (inputCnf : ICnf) (nVars : Nat) : Except CheckerError State := do
  let ⟨initPog, hInitPog⟩ ← initialPog nVars
  let ⟨initDv, allVars_eq, hInitDv⟩ := initialDepVars inputCnf
  let st := {
    inputCnf
    clauseDb := .ofICnf inputCnf
    -- TODO: actually figure this number out while parsing or otherwise
    up := .new (2^20)
    pogDefs := .empty ClauseIdx
    pog := initPog
    depVars := initDv
    root := none
  }
  have pogDefs'_empty : st.pogDefs' = ∅ := by
    simp [PreState.pogDefs']
  have pogDefsTerm_tr : st.pogDefsTerm = ⊤ := by
    rw [PreState.pogDefsTerm, pogDefs'_empty, Finset.coe_empty]
    apply ClauseDb.toPropFunSub_emptySet
  have allVars_eq : st.allVars = st.inputCnf.toPropForm.vars := allVars_eq
  have pfs := {
    pogDefs_in_clauseDb := by
      simp [pogDefs'_empty]
    depVars_pog := by
      intro x D hFind
      simp [hInitPog, PropForm.vars, hInitDv x D hFind]
    partitioned := by
      simp [hInitPog, partitioned]
    clauseDb_semVars_sub := by
      rw [allVars_eq, ClauseDb.toPropFun_ofICnf, ← Cnf.mk_toPropForm]
      apply PropForm.semVars_subset_vars
    pogDefsTerm_semVars_sub := by
      rw [pogDefsTerm_tr, PropFun.semVars_tr, Finset.coe_empty]
      apply Set.empty_subset
    inputCnf_vars_sub := by
      rw [allVars_eq]
    equivalent_clauseDb := by
      rw [ClauseDb.toPropFun_ofICnf]
      apply PropFun.equivalentOver_refl
    pog_vars := by
      rw [allVars_eq]
      simp [hInitPog, PropForm.vars]
    extends_pogDefsTerm := fun σ =>
      ⟨σ, PropAssignment.agreeOn_refl _ _, by rw [pogDefsTerm_tr]; simp⟩
    uep_pogDefsTerm := by
      simp only [pogDefsTerm_tr, PropFun.semVars_tr, Finset.coe_empty, allVars_eq]
      exact PropFun.hasUniqueExtension_refl _ _
    equivalent_lits := by
      rw [pogDefsTerm_tr]
      simp [hInitPog, PropFun.equivalentOver_refl]
  }
  return ⟨st, pfs⟩

/-- Check if `C` is an asymmetric tautology wrt the clause database. -/
def checkAsymmTautoHinted (db : ClauseDb ClauseIdx) (up : PPA) (C : IClause)
    (hints : Array ClauseIdx) :
    Except CheckerError { _up : PPA // db.toPropFunSub (· ∈ hints.data) ≤ C.toPropFun }
:= do
  let (up', res) := db.propagateUnitsHinted up C hints
  match res with
  | .contradiction h => return ⟨up', by
    have := le_himp_iff.mpr h
    simpa using this⟩
  | .extended => throw <| .upNoContradiction
  | .hintNotUnit idx C => throw <| .hintNotUnit idx C
  | .hintNonexistent idx => throw <| .unknownClauseIdx idx

/-- Check if `C` is an asymmetric tautology wrt the clause database, or simply a tautology. -/
def checkImpliedHinted (db : ClauseDb ClauseIdx) (up : PPA) (C : IClause) (hints : Array ClauseIdx) :
    Except CheckerError { _up : PPA // db.toPropFunSub (· ∈ hints.data) ≤ C.toPropFun }
:= do
  let (up', b) := up.checkTauto C
  -- Checking for tautologies is not necessary to ensure the correctness of UP,
  -- but it is needed to accept CPOG proofs that add or delete tautological clauses,
  -- since our UP procedure will not reach a contradiction from such clauses.
  if h : b = true then
    .ok ⟨up', by simp [b.property.mp h]⟩
  else
    checkAsymmTautoHinted db up' C hints

def addClause (db₀ : ClauseDb ClauseIdx) (idx : ClauseIdx) (C : IClause) :
    Except CheckerError { db : ClauseDb ClauseIdx //
      db = db₀.addClause idx C ∧
      ¬db₀.contains idx ∧
      -- This is just for convenience as it can be proven directly from the other postconditions.
      db.toPropFun = db₀.toPropFun ⊓ C.toPropFun } := do
  if h : db₀.contains idx then
    throw <| .duplicateClauseIdx idx
  else
    return ⟨db₀.addClause idx C, rfl, h, db₀.toPropFun_addClause_eq idx C h⟩

def addAt (idx : ClauseIdx) (C : IClause) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨up', hImp⟩ ← checkImpliedHinted st.clauseDb st.up C hints
  let ⟨db', hAdd, hContains, hEq⟩ ← addClause st.clauseDb idx C
  let st' := { st with clauseDb := db', up := up' }
  have hDb : st'.clauseDb.toPropFun = st.clauseDb.toPropFun := by
    simp [hEq, st.clauseDb.toPropFun_subset _ |>.trans hImp]
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm := by
    have hMem : idx ∉ (st.pogDefs' : Set _) := fun h =>
      hContains (pfs.pogDefs_in_clauseDb _ h)
    have : st'.pogDefs' = st.pogDefs' := rfl
    rw [PreState.pogDefsTerm, this]
    simp [PreState.pogDefsTerm, hAdd, st.clauseDb.toPropFunSub_addClause_of_not_mem C hMem]
  have pfs' := { pfs with
    pogDefs_in_clauseDb := fun idx h => by
      have := pfs.pogDefs_in_clauseDb idx h
      simp only [hAdd]
      exact st.clauseDb.contains_addClause _ _ _ |>.mpr (Or.inl this)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    clauseDb_semVars_sub := hDb ▸ pfs.clauseDb_semVars_sub
    pogDefsTerm_semVars_sub := hPogDefs ▸ pfs.pogDefsTerm_semVars_sub
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    extends_pogDefsTerm := hPogDefs ▸ pfs.extends_pogDefsTerm
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  set (σ := State) ⟨st', pfs'⟩

def getClause (db : ClauseDb ClauseIdx) (idx : ClauseIdx) :
    Except CheckerError { C : IClause // db.getClause idx = some C } :=
  match db.getClause idx with
  | some C => return ⟨C, rfl⟩
  | none => throw <| .unknownClauseIdx idx

def delAt (idx : ClauseIdx) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨C, hGet⟩ ← getClause st.clauseDb idx
  -- NOTE: We could investigate whether the check is really necessary.
  let ⟨_, hMem⟩ ← (if h : st.pogDefs.contains idx then
      throw <| .pogDefClause idx
    else
      pure ⟨(), HashSet.not_mem_toFinset _ _ |>.mpr h⟩
    : Except CheckerError { _u : Unit // idx ∉ st.pogDefs' })
  let db' := st.clauseDb.delClause idx
  -- The clause is AT by everything except itself.
  let ⟨up', hImp⟩ ← checkImpliedHinted db' st.up C hints
  let st' := { st with clauseDb := db', up := up' }
  have hDb : st'.clauseDb.toPropFun = st.clauseDb.toPropFun := by
    have : st'.clauseDb.toPropFun = st'.clauseDb.toPropFun ⊓ C.toPropFun := by
      have := st'.clauseDb.toPropFun_subset _ |>.trans hImp
      exact left_eq_inf.mpr this
    rw [this]
    simp [st.clauseDb.toPropFun_delClause_eq _ _ hGet]
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm :=
    st.clauseDb.toPropFunSub_delClause_of_not_mem hMem
  have pfs' := { pfs with
    pogDefs_in_clauseDb := fun idx h => by
      refine st.clauseDb.contains_delClause _ _ |>.mpr ⟨pfs.pogDefs_in_clauseDb idx h, ?_⟩
      intro hEq
      exact hMem (hEq.symm ▸ h)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    clauseDb_semVars_sub := hDb ▸ pfs.clauseDb_semVars_sub
    pogDefsTerm_semVars_sub := hPogDefs ▸ pfs.pogDefsTerm_semVars_sub
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    extends_pogDefsTerm := hPogDefs ▸ pfs.extends_pogDefsTerm
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  set (σ := State) ⟨st', pfs'⟩

def ensureFreshVar (st : PreState) (x : Var) : Except CheckerError { _u : Unit //
    x ∉ st.allVars } := do
  if h : st.depVars.contains x then
    throw <| .duplicateExtVar x
  else
    return ⟨(), h⟩

def getDeps (st : PreState) (pfs : st.WF) (l : ILit) : Except CheckerError { D : RBSet Var compare //
    l.var ∈ st.allVars ∧
    ∀ y ∈ (st.pog.toPropForm l).vars, y ∈ D } := do
  match h : st.depVars.find? l.var with
  | some D =>
    return ⟨D, st.depVars.contains_iff _ |>.mpr ⟨D, h⟩, pfs.depVars_pog' _ _ h⟩
  | none => throw <| .unknownVar l.var

def getDepsArray {st : PreState} (pfs : st.WF) (ls : Array ILit) :
    Except CheckerError { Ds : Array (RBSet Var compare) //
      (∀ l ∈ ls.data, l.var ∈ st.allVars) ∧
      Ds.size = ls.size ∧
      ∀ (i : Nat) (hI : i < ls.size) (hI' : i < Ds.size),
        ∀ y ∈ (st.pog.toPropForm ls[i]).vars, y ∈ Ds[i] } :=
  let f l :=
    match st.depVars.find? l.var with
    | some D => return D
    | none => throw <| .unknownVar l.var
  let x : Except CheckerError (Array (RBSet Var compare)) := ls.mapM f
  match h : x with
  | .error e => throw e
  | .ok Ds =>
    have := Array.SatisfiesM_mapM (as := ls) (f := f)
      -- Postcondition on the input
      (motive := fun i => ∀ (j : Fin ls.size), j < i → ls[j].var ∈ st.allVars)
      -- Postcondition on the outputs
      (p := fun i val => ∀ y ∈ (st.pog.toPropForm ls[i]).vars, y ∈ val)
      (h0 := by simp)
      (hs := by
        dsimp
        intro i ih
        split
        next h =>
          simp only [SatisfiesM_Except_eq]
          intro D hEq
          cases hEq
          refine ⟨pfs.depVars_pog' _ _ h, ?_⟩
          intro j hJ
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJ) with
          | inl hJ => exact ih j hJ
          | inr hJ =>
            simp only [hJ]
            exact st.depVars.contains_iff _ |>.mpr ⟨_, h⟩
        . simp)
    have hLs := by
      intro l hL
      simp only [SatisfiesM_Except_eq] at this
      have ⟨h, _⟩ := this _ h
      have ⟨i, hI⟩ := Array.get_of_mem_data hL
      exact hI ▸ h i i.isLt
    have hDs := by
      simp only [SatisfiesM_Except_eq] at this
      have := this _ h
      aesop
    have hSz := by
      apply SatisfiesM_Except_eq.mp ?_ _ h
      apply Array.size_mapM
    return ⟨Ds, hLs, hSz, hDs⟩

def addPogDefClause (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (C : IClause) (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropFun = db₀.toPropFun ⊓ C.toPropFun ∧
      p.1.toPropFunSub (· ∈ p.2.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓ C.toPropFun ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨db, hAdd, hNContains, hDb⟩ ← addClause db₀ idx C
  let pd := pd₀.insert idx

  have hMem : idx ∈ pd.toFinset := by simp
  have hContainsTrans : ∀ {idx}, db₀.contains idx → db.contains idx := fun h => by
    rw [hAdd]
    exact db₀.contains_addClause _ _ _ |>.mpr (Or.inl h)
  have hContains : db.contains idx := by
    rw [hAdd]
    exact db₀.contains_addClause _ _ _ |>.mpr (Or.inr rfl)
  have hHelper : db₀.toPropFunSub (· ∈ pd.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) := by
    apply db₀.toPropFunSub_subset_eq fun _ hMem => by simp; exact Or.inr hMem
    intro idx hMem hContains
    simp at hMem
    cases hMem with
    | inl h =>
      exfalso
      exact hNContains (h ▸ hContains)
    | inr hMem => exact hMem
  have hPd : db.toPropFunSub (· ∈ pd.toFinset) =
      db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓ C.toPropFun := by
    rw [← hHelper, hAdd]
    exact db₀.toPropFunSub_addClause_eq _ hMem hNContains
  have hPdDb : ∀ idx, idx ∈ pd.toFinset → db.contains idx := by
    simp only [HashSet.toFinset_insert, Finset.mem_singleton, Finset.mem_insert]
    intro _ h
    cases h with
    | inl h => exact h ▸ hContains
    | inr hMem => exact hContainsTrans (h _ hMem)

  return ⟨(db, pd), hDb, hPd, hPdDb⟩

theorem def_ext_correct {st : PreState} (H : st.WF) (st' : PreState) (x : Var) (φ ψ : PropFun Var)
    (hDb : st'.clauseDb.toPropFun = st.clauseDb.toPropFun ⊓ (.biImpl (.var x) φ))
    (hPd : st'.pogDefsTerm = st.pogDefsTerm ⊓ (.biImpl (.var x) φ))
    (hAv : st'.allVars = insert x st.allVars)
    (hPog₁ : ∀ y, x ≠ y → st'.pog.toPropForm (.mkPos y) = st.pog.toPropForm (.mkPos y))
    (hPog₂ : ⟦st'.pog.toPropForm (.mkPos x)⟧ = ψ)
    (hEquiv : PropFun.equivalentOver st.inputCnf.toPropForm.vars (.var x ⊓ st'.pogDefsTerm) ψ)
    (hφ : ↑φ.semVars ⊆ st.allVars)
    (hX : x ∉ st.allVars) :
    (PropFun.equivalentOver st.inputCnf.toPropForm.vars
      st.inputCnf.toPropFun st'.clauseDb.toPropFun ∧
    (∀ σ₁, ∃ (σ₂ : PropAssignment Var),
      σ₂.agreeOn st.inputCnf.toPropForm.vars σ₁ ∧ σ₂ ⊨ st'.pogDefsTerm) ∧
    PropFun.hasUniqueExtension st.inputCnf.toPropForm.vars st'.allVars st'.pogDefsTerm ∧
    ∀ x, PropFun.equivalentOver st.inputCnf.toPropForm.vars
      (.var x ⊓ st'.pogDefsTerm) ⟦st'.pog.toPropForm (.mkPos x)⟧) :=
  have hEquivAv : PropFun.equivalentOver st.allVars st.clauseDb.toPropFun st'.clauseDb.toPropFun
      := by
    rw [hDb]
    exact equivalentOver_def_ext st.clauseDb.toPropFun φ (H.clauseDb_semVars_sub) hφ hX
  have equiv :=
    H.equivalent_clauseDb.trans (hEquivAv.subset H.inputCnf_vars_sub)
  have hUepInsert :=
    hasUniqueExtension_def_ext x st.pogDefsTerm φ hφ
  have extend := by
    intro σ
    have ⟨σ₁, hAgree, h₁⟩ := H.extends_pogDefsTerm σ
    let σ₂ := σ₁.set x (φ.eval σ₁)
    have hAgree₂₁ : σ₂.agreeOn st.allVars σ₁ := PropAssignment.agreeOn_set_of_not_mem _ _ hX
    have : σ₂ ⊨ st.pogDefsTerm :=
      agreeOn_semVars (hAgree₂₁.subset H.pogDefsTerm_semVars_sub) |>.mpr h₁
    have : σ₂ ⊨ φ ↔ σ₁ ⊨ φ := agreeOn_semVars (hAgree₂₁.subset hφ)
    exact ⟨σ₂, hAgree₂₁.subset H.inputCnf_vars_sub |>.trans hAgree, by aesop⟩
  have uep := by
    rw [hAv, hPd]
    exact H.uep_pogDefsTerm.conj_right _ |>.trans hUepInsert
  have hEquivVarNe : ∀ {y : Var}, x ≠ y → PropFun.equivalentOver st.allVars
      (.var y ⊓ st'.pogDefsTerm) (.var y ⊓ st.pogDefsTerm) := by
    intro y hEq
    suffices PropFun.equivalentOver (st.allVars ∪ {y})
        (.var y ⊓ st'.pogDefsTerm) (.var y ⊓ st.pogDefsTerm) from
      this.subset (Set.subset_union_left _ _)
    rw [hPd, ← inf_assoc]
    apply PropFun.equivalentOver.symm
    have hX : x ∉ st.allVars ∪ {y} := by simp [hEq, hX]
    apply equivalentOver_def_ext _ _ ?_ (hφ.trans <| Set.subset_union_left _ _) hX
    suffices ↑((PropFun.var y).semVars ∪ st.pogDefsTerm.semVars) ⊆ st.allVars ∪ {y} from
      subset_trans (PropFun.semVars_conj _ _) this
    intro y; simp
    intro h; cases h with
    | inl hEq => exact Or.inl hEq
    | inr hMem => exact Or.inr (H.pogDefsTerm_semVars_sub hMem)
  have equiv_vars := by
    intro y
    by_cases hEq : x = y
    case neg =>
      rw [hPog₁ _ hEq]
      exact (hEquivVarNe hEq).subset H.inputCnf_vars_sub |>.trans (H.equivalent_lits y)
    case pos =>
      rw [← hEq, hPog₂]
      exact hEquiv
  ⟨equiv, extend, uep, equiv_vars⟩

def addPogDefClauses (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (ls : Array ILit) (f : ILit → IClause)
    (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropFun = db₀.toPropFun ⊓
        arrayConjTerm (ls.map fun l => (f l).toPropForm) ∧
      p.1.toPropFunSub (· ∈ p.2.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓
        arrayConjTerm (ls.map fun l => (f l).toPropForm) ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨out, h₁, h₂, h₃⟩ ← loopM_with_invariant (State := ClauseDb ClauseIdx × HashSet ClauseIdx)
    (n := ls.size)
    (invariant := fun i ⟨db, pd⟩ =>
      db.toPropFun = db₀.toPropFun ⊓
        listConjTerm (ls.data.take i |>.map fun l => (f l).toPropFun) ∧
      db.toPropFunSub (· ∈ pd.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓
        listConjTerm (ls.data.take i |>.map fun l => (f l).toPropFun) ∧
      ∀ idx, idx ∈ pd.toFinset → db.contains idx)
    (start_state := ⟨(db₀, pd₀), by simp, by simp, h⟩)
    (step := fun i ⟨(db, pd), ih₁, ih₂, ih₃⟩ => do
      let l := ls[i]
      let ⟨st', hDb, hPd, h⟩ ← addPogDefClause db pd (idx+i+1) (f l) ih₃
      have hEquiv :
          listConjTerm (ls.data.take (i + 1) |>.map fun l => (f l).toPropFun) =
          listConjTerm (ls.data.take i |>.map fun l => (f l).toPropFun) ⊓
            (f l).toPropFun := by
        ext
        simp [satisfies_listConjTerm, List.take_succ, List.get?_eq_get i.isLt,
          Array.getElem_eq_data_get]
        constructor
        . aesop
        . intro ⟨h₁, h₂⟩ φ h
          cases h with
          | inl h =>
            have ⟨l, hL, hφ⟩ := h
            exact hφ ▸ h₁ l hL
          | inr h =>
            simp_all
      have hDb' := by rw [hDb, ih₁, inf_assoc, hEquiv]
      have hPd' := by rw [hPd, ih₂, inf_assoc, hEquiv]
      return ⟨st', hDb', hPd', h⟩)
  have hDb := by
    simp only [List.take_length] at h₁
    simp [arrayConjTerm_eq_listConjTerm_data, Function.comp, h₁]
  have hPd := by
    simp only [List.take_length] at h₂
    simp [arrayConjTerm_eq_listConjTerm_data, Function.comp, h₂]
  return ⟨out, hDb, hPd, h₃⟩

def addProdClauses (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (x : Var) (ls : Array ILit)
    (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropFun = db₀.toPropFun ⊓
        (.biImpl (.var x) ⟦arrayConj (ls.map ILit.toPropForm)⟧) ∧
      p.1.toPropFunSub (· ∈ p.2.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓
        (.biImpl (.var x) ⟦arrayConj (ls.map ILit.toPropForm)⟧) ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨(db₁, pd₁), hDb₁, hPd₁, h₁⟩ ← addPogDefClause db₀ pd₀ idx (ls.map (-·) |>.push (.mkPos x)) h
  let ⟨(db₂, pd₂), hDb₂, hPd₂, h₂⟩ ← addPogDefClauses db₁ pd₁ idx ls (#[.mkNeg x, ·]) h₁
  have hEquiv :
      Clause.toPropFun (ls.map (-·) |>.push (.mkPos x)) ⊓
      arrayConjTerm (ls.map (Clause.toPropForm #[ILit.mkNeg x, ·])) =
      .biImpl (var x) ⟦arrayConj (ls.map ILit.toPropForm)⟧ := by
    ext τ
    simp [-satisfies_mk, satisfies_arrayConjTerm, Clause.satisfies_iff]
    refine ⟨?mp, ?mpr⟩
    case mp =>
      intro ⟨_, h⟩
      have h : ∀ (l : ILit), l ∈ ls.data → τ ⊭ .var x ∨ τ ⊨ LitVar.toPropFun l := fun l hL => by
        have := h l hL
        rw [Clause.satisfies_iff] at this
        simp_all
      cases h : τ x <;>
        aesop
    case mpr =>
      intro h
      refine ⟨?_, fun l hL => Clause.satisfies_iff.mpr ?_⟩
      . cases hx : τ x
        . simp only [hx, false_iff, not_forall, exists_prop] at h
          have ⟨l, hl, hτl⟩ := h
          refine ⟨-l, Or.inl ⟨l, hl, rfl⟩, ?_⟩
          simpa
        . use ILit.mkPos x
          simp [hx]
      . cases hx : τ x
        . use ILit.mkNeg x
          simp [hx]
        . use l
          have := h.mp hx _ hL
          simpa
  have hDb := by
    rw [hDb₂, hDb₁, inf_assoc, hEquiv]
  have hPd := by
    rw [hPd₂, hPd₁, inf_assoc, hEquiv]
  return ⟨(db₂, pd₂), hDb, hPd, h₂⟩

def addConjToPog (g : Pog) (x : Var) (ls : Array ILit) : Except CheckerError { g' : Pog //
    g.addConj x ls = .ok g' } :=
  match g.addConj x ls with
  | .ok g' => pure ⟨g', rfl⟩
  | .error e => throw <| .graphUpdateError e

def disjointUnion (ls : Array ILit) (Ds : Array (RBSet Var compare)) :
    Except CheckerError { U : RBSet Var compare //
      (∀ x, x ∈ U ↔ ∃ D ∈ Ds.data, x ∈ D) ∧
      ∀ (i j : Nat) (hI : i < Ds.size) (hJ : j < Ds.size), i ≠ j →
        ∀ x ∈ Ds[i], x ∉ Ds[j] } :=
  match h : RBSet.disjointUnion Ds with
  | (U, true) =>
    have h₁ : (RBSet.disjointUnion Ds).fst = U := congrArg Prod.fst h
    have h₂ : (RBSet.disjointUnion Ds).snd = true := congrArg Prod.snd h
    return ⟨U, h₁ ▸ RBSet.mem_disjointUnion Ds, RBSet.disjoint_disjointUnion Ds h₂⟩
  | (_, false) =>
    throw <| .depsNotDisjoint (ls.toList.map ILit.var)

def addProd (idx : ClauseIdx) (x : Var) (ls : Array ILit) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  let ⟨_, hX⟩ ← ensureFreshVar st x

  -- Check that variables are known and compute their dependencies.
  let ⟨Ds, hLs, hSz, hDs⟩ ← getDepsArray pfs ls

  -- Compute total dependency set and check pairwise disjointness.
  let ⟨U, hU, hDisjoint⟩ ← disjointUnion ls Ds

  let ⟨pog', hPog⟩ ← addConjToPog st.pog x ls

  let ⟨(db', pd'), hDb, hPd, pogDefs_in_clauseDb⟩ ←
    addProdClauses st.clauseDb st.pogDefs idx x ls pfs.pogDefs_in_clauseDb

  let st' := { st with
    clauseDb := db'
    pogDefs := pd'
    pog := pog'
    depVars := st.depVars.insert x U
  }

  have hPd : st'.pogDefsTerm = st.pogDefsTerm ⊓
      (.biImpl (.var x) ⟦arrayConj (ls.map ILit.toPropForm)⟧) := hPd

  have hDb : st'.clauseDb.toPropFun = st.clauseDb.toPropFun ⊓
      (.biImpl (.var x) ⟦arrayConj (ls.map ILit.toPropForm)⟧) := hDb

  have hVars : ∀ x ∈ (arrayConj (ls.map st.pog.toPropForm)).vars, x ∈ U := by
    intro x
    simp only [mem_vars_arrayConj, getElem_fin, Array.getElem_map]
    intro ⟨i, hMem⟩
    have hI : i < ls.size := Array.size_map st.pog.toPropForm ls ▸ i.isLt
    have := hDs i hI (hSz ▸ hI) _ hMem
    exact hU x |>.mpr ⟨_, Array.getElem_mem_data _ _, this⟩

  have hSemVars : ↑(PropFun.semVars ⟦arrayConj (ls.map ILit.toPropForm)⟧) ⊆ st.allVars :=
    by
      apply subset_trans (Finset.coe_subset.mpr <| PropForm.semVars_subset_vars _)
      intro x
      simp only [Finset.mem_coe, mem_vars_arrayConj, getElem_fin, Array.getElem_map,
        LitVar.vars_toPropForm, Finset.mem_singleton]
      intro ⟨i, h⟩
      exact h ▸ hLs ls[i] (Array.getElem_mem_data _ _)

  have hAv : st'.allVars = insert x st.allVars := by
    ext
    simp [PreState.allVars, HashMap.contains_insert, @eq_comm _ x, or_comm]

  have ⟨equivalent_clauseDb, extends_pogDefsTerm, uep_pogDefsTerm, equivalent_lits⟩ :=
    def_ext_correct pfs st'
      x ⟦arrayConj (ls.map ILit.toPropForm)⟧ ⟦arrayConj (ls.map st.pog.toPropForm)⟧
      hDb hPd hAv
      (fun l hNe => st.pog.toPropForm_addConj_lit_of_ne _ _ _ _ (by exact hPog) hNe)
      (by simp [st.pog.toPropForm_addConj _ _ _ hPog])
      (by
        rw [hPd]
        exact addConj_new_var_equiv
          st.pog st.pogDefsTerm ls
          hX pfs.inputCnf_vars_sub pfs.pogDefsTerm_semVars_sub pfs.uep_pogDefsTerm
          pfs.extends_pogDefsTerm
          fun l hL =>
            have hMem := hLs l hL
            ⟨hMem, pfs.pog_semVars l hMem, pfs.equivalent_lits' l hMem⟩)
      hSemVars hX

  have pfs' := {
    pogDefs_in_clauseDb
    clauseDb_semVars_sub := by
      rw [hAv, hDb]
      apply subset_trans (Finset.coe_subset.mpr <| semVars_conj _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . exact subset_trans pfs.clauseDb_semVars_sub (Set.subset_insert _ _)
      apply subset_trans (Finset.coe_subset.mpr <| semVars_biImpl _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . simp
      exact subset_trans hSemVars (Set.subset_insert _ _)
    pogDefsTerm_semVars_sub := by
      rw [hAv, hPd]
      apply subset_trans (Finset.coe_subset.mpr <| semVars_conj _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . exact subset_trans pfs.pogDefsTerm_semVars_sub (Set.subset_insert _ _)
      apply subset_trans (Finset.coe_subset.mpr <| semVars_biImpl _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . simp
      exact subset_trans hSemVars (Set.subset_insert _ _)
    inputCnf_vars_sub :=
      hAv ▸ pfs.inputCnf_vars_sub.trans (Set.subset_insert x st.allVars)
    depVars_pog := by
      intro y D hFind
      by_cases hEq : x = y
      . rw [st.pog.toPropForm_addConj _ _ _ (hEq ▸ hPog)]
        rw [st.depVars.find?_insert _ (beq_iff_eq _ _ |>.mpr hEq)] at hFind
        injection hFind with hFind
        exact hFind ▸ hVars
      . rw [st.pog.toPropForm_addConj_of_ne _ _ _ _ hPog hEq]
        rw [st.depVars.find?_insert_of_ne _ (bne_iff_ne _ _ |>.mpr hEq)] at hFind
        exact pfs.depVars_pog y D hFind
    pog_vars := by
      intro y hMem
      simp only [hAv, Set.mem_insert_iff] at hMem
      cases hMem with
      | inl hEq =>
        intro x
        simp only [hEq, st.pog.toPropForm_addConj _ _ _ hPog, mem_vars_arrayConj,
          getElem_fin, Array.getElem_map]
        intro ⟨i, hMem⟩
        refine pfs.pog_vars' ls[i] ?_ hMem
        exact hLs ls[i.val] (Array.getElem_mem_data _ _)
      | inr hMem =>
        have hNe : x ≠ y := fun h => absurd hMem (h ▸ hX)
        rw [st.pog.toPropForm_addConj_of_ne _ _ _ _ hPog hNe]
        exact pfs.pog_vars y hMem
    partitioned := by
      intro y
      by_cases hEq : x = y
      . rw [st.pog.toPropForm_addConj _ _ _ (hEq ▸ hPog), partitioned_arrayConj]
        intro i
        simp only [getElem_fin, Array.getElem_map]
        constructor
        . exact pfs.partitioned' (ls[i.val])
        . intro j hNe
          have h := Array.size_map st.pog.toPropForm ls
          have h' := h.trans hSz.symm
          have hI := hDs i (h ▸ i.isLt) (h' ▸ i.isLt)
          have hJ := hDs j (h ▸ j.isLt) (h' ▸ j.isLt)
          have hIJ := hDisjoint i j (h' ▸ i.isLt) (h' ▸ j.isLt) (Fin.val_ne_of_ne hNe)
          simp at hI hJ hIJ ⊢
          apply Finset.subset_empty.mp
          intro x hX
          exfalso
          have ⟨hXI, hXJ⟩ := Finset.mem_inter.mp hX
          exact hIJ _ (hI _ hXI) (hJ _ hXJ)
      . rw [st.pog.toPropForm_addConj_of_ne _ _ _ _ hPog hEq]
        exact pfs.partitioned y
    equivalent_clauseDb
    extends_pogDefsTerm
    uep_pogDefsTerm
    equivalent_lits
  }
  set (σ := State) ⟨st', pfs'⟩

def addSumClauses (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropFun = db₀.toPropFun ⊓
        (.biImpl (.var x) (LitVar.toPropFun l₁ ⊔ LitVar.toPropFun l₂)) ∧
      p.1.toPropFunSub (· ∈ p.2.toFinset) = db₀.toPropFunSub (· ∈ pd₀.toFinset) ⊓
        (.biImpl (.var x) (LitVar.toPropFun l₁ ⊔ LitVar.toPropFun l₂)) ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨(db₁, pd₁), hDb₁, hPd₁, h⟩ ← addPogDefClause db₀ pd₀ idx     #[.mkNeg x, l₁, l₂] h
  let ⟨(db₂, pd₂), hDb₂, hPd₂, h⟩ ← addPogDefClause db₁ pd₁ (idx+1) #[.mkPos x, -l₁]    h
  let ⟨(db₃, pd₃), hDb₃, hPd₃, h⟩ ← addPogDefClause db₂ pd₂ (idx+2) #[.mkPos x, -l₂]    h
  have hDb := by
    rw [hDb₃, hDb₂, hDb₁]
    simp [Clause.toPropFun, inf_assoc, disj_def_eq]
  have hPd := by
    rw [hPd₃, hPd₂, hPd₁]
    simp [Clause.toPropFun, inf_assoc, disj_def_eq]
  return ⟨(db₃, pd₃), hDb, hPd, h⟩

def ensurePogHints (st : PreState) (hints : Array ClauseIdx) :
    Except CheckerError { _u : Unit //
      ∀ idx, idx ∈ hints.data → idx ∈ st.pogDefs' } := do
  match hSz : hints.size with
  | 0 =>
    return ⟨(), fun _ hMem => by
      rw [Array.size] at hSz
      rw [List.length_eq_zero.mp hSz] at hMem
      contradiction⟩
  | i+1 =>
    let ⟨_, h⟩ ← go i (hSz ▸ Nat.lt_succ_self _) (fun j hLt => by
      have := j.isLt
      linarith)
    return ⟨(), fun _ hMem => have ⟨i, hI⟩ := Array.get_of_mem_data hMem; hI ▸ h i⟩
where go (i : Nat) (hLt : i < hints.size)
    (ih : ∀ (j : Fin hints.size), i < j → hints[j] ∈ st.pogDefs') :
    Except CheckerError { _u : Unit // ∀ (j : Fin hints.size), hints[j] ∈ st.pogDefs' } := do
  let idx := hints[i]
  if hContains : st.pogDefs.contains idx then
    have hContains : hints[i] ∈ st.pogDefs' :=
      by simp [PreState.pogDefs', HashSet.mem_toFinset, hContains]
    match hI : i, hLt, ih with
    | 0, hLt, ih =>
      return ⟨(), fun j => by
        cases j.val.eq_zero_or_pos with
        | inl hEq =>
          -- Why does this compute a correct motive while `rw` doesn't?
          simp only [hI] at hContains
          simp [hEq, hContains]
        | inr hLt =>
          exact ih j hLt⟩
    | i+1, hLt, ih =>
      by exact -- Hmmm
        go i (Nat.lt_of_succ_lt hLt) (fun j hLt => by
          cases Nat.eq_or_lt_of_le hLt with
          | inl hEq =>
            simp only [hI] at hContains
            simp [← hEq, hContains]
          | inr hLt =>
            exact ih j hLt)
  else
    throw <| .hintNotPog idx

def addDisjToPog (g : Pog) (x : Var) (l₁ l₂ : ILit) : Except CheckerError { g' : Pog //
    g.addDisj x l₁ l₂ = .ok g' } :=
  match g.addDisj x l₁ l₂ with
  | .ok g' => pure ⟨g', rfl⟩
  | .error e => throw <| .graphUpdateError e

def addSum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (hints : Array ClauseIdx) :
    CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  let ⟨_, hX⟩ ← ensureFreshVar st x

  -- Check that variables are known and compute their dependencies.
  let ⟨D₁, hL₁, hD₁⟩ ← getDeps st pfs l₁
  let ⟨D₂, hL₂, hD₂⟩ ← getDeps st pfs l₂

  -- Check that POG defs imply that the children have no models in common.
  let ⟨_, hHints⟩ ← ensurePogHints st hints
  -- NOTE: Important that this be done before adding clauses, for linearity.
  let ⟨up', hImp⟩ ← checkImpliedHinted st.clauseDb st.up #[-l₁, -l₂] hints

  let ⟨pog', hPog⟩ ← addDisjToPog st.pog x l₁ l₂

  let ⟨(db', pd'), hDb, hPd, pogDefs_in_clauseDb⟩ ←
    addSumClauses st.clauseDb st.pogDefs idx x l₁ l₂ pfs.pogDefs_in_clauseDb

  let st' := { st with
    up := up'
    clauseDb := db'
    pogDefs := pd'
    pog := pog'
    depVars := st.depVars.insert x (D₁.union D₂)
  }

  have hPd : st'.pogDefsTerm = st.pogDefsTerm ⊓ (.biImpl (.var x) (LitVar.toPropFun l₁ ⊔ LitVar.toPropFun l₂))
    := hPd

  have hDb : st'.clauseDb.toPropFun = st.clauseDb.toPropFun ⊓
      (.biImpl (.var x) (LitVar.toPropFun l₁ ⊔ LitVar.toPropFun l₂)) :=
    hDb

  have hDisjoint : st.pogDefsTerm ⊓ LitVar.toPropFun l₁ ⊓ LitVar.toPropFun l₂ ≤ ⊥ := by
    have : st.pogDefsTerm ≤ st.clauseDb.toPropFunSub (· ∈ hints.data) :=
      st.clauseDb.toPropFunSub_subset hHints
    rw [inf_assoc, ← le_himp_iff]
    have := le_trans this hImp
    simp [Clause.toPropFun] at this
    simp [this]

  have hSemVars : ↑(LitVar.toPropFun l₁ ⊔ LitVar.toPropFun l₂).semVars ⊆ st.allVars := by
    have : ↑((LitVar.toPropFun l₁).semVars ∪ (LitVar.toPropFun l₂).semVars) ⊆ st.allVars := by
      intro x h
      simp at h
      cases h <;> next h => simp only [h, hL₁, hL₂]
    exact subset_trans (PropFun.semVars_disj _ _) this

  have hAv : st'.allVars = insert x st.allVars := by
    ext
    simp [PreState.allVars, HashMap.contains_insert, @eq_comm _ x, or_comm]

  have ⟨equivalent_clauseDb, extends_pogDefsTerm, uep_pogDefsTerm, equivalent_lits⟩ :=
    def_ext_correct pfs st'
      x ((LitVar.toPropFun l₁) ⊔ (LitVar.toPropFun l₂)) (⟦st.pog.toPropForm l₁⟧ ⊔ ⟦st.pog.toPropForm l₂⟧)
      hDb hPd hAv
      (fun l hNe => st.pog.toPropForm_addDisj_lit_of_ne _ _ _ _ _ (by exact hPog) hNe)
      (by simp [st.pog.toPropForm_addDisj _ _ _ _ hPog])
      (by
        rw [hPd, ← inf_assoc]
        exact addDisj_new_var_equiv st.pogDefsTerm (LitVar.toPropFun l₁) (LitVar.toPropFun l₂) _ _ hX
          (pfs.inputCnf_vars_sub) (pfs.pogDefsTerm_semVars_sub)
          (by simp [hL₁]) (by simp [hL₂])
          (pfs.equivalent_lits' l₁ hL₁) (pfs.equivalent_lits' l₂ hL₂))
      hSemVars hX

  have pfs' := {
    pogDefs_in_clauseDb
    clauseDb_semVars_sub := by
      rw [hAv, hDb]
      apply subset_trans (Finset.coe_subset.mpr <| semVars_conj _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . exact subset_trans pfs.clauseDb_semVars_sub (Set.subset_insert _ _)
      apply subset_trans (Finset.coe_subset.mpr <| semVars_biImpl _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . simp
      exact subset_trans hSemVars (Set.subset_insert _ _)
    pogDefsTerm_semVars_sub := by
      rw [hAv, hPd]
      apply subset_trans (Finset.coe_subset.mpr <| semVars_conj _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . exact subset_trans pfs.pogDefsTerm_semVars_sub (Set.subset_insert _ _)
      apply subset_trans (Finset.coe_subset.mpr <| semVars_biImpl _ _)
      rw [Finset.coe_union]
      apply Set.union_subset
      . simp
      exact subset_trans hSemVars (Set.subset_insert _ _)
    inputCnf_vars_sub :=
      hAv ▸ pfs.inputCnf_vars_sub.trans (Set.subset_insert x st.allVars)
    depVars_pog := by
      intro y D hFind
      by_cases hEq : x = y
      . rw [st.pog.toPropForm_addDisj _ _ _ _ (hEq ▸ hPog)]
        rw [st.depVars.find?_insert _ (beq_iff_eq _ _ |>.mpr hEq)] at hFind
        injection hFind with hFind
        simp_rw [PropForm.vars, ← hFind, RBSet.mem_union, Finset.mem_union]
        tauto
      . rw [st.pog.toPropForm_addDisj_of_ne _ _ _ _ _ hPog hEq]
        rw [st.depVars.find?_insert_of_ne _ (bne_iff_ne _ _ |>.mpr hEq)] at hFind
        exact pfs.depVars_pog y D hFind
    pog_vars := by
      intro y hMem
      simp only [hAv, Set.mem_insert_iff] at hMem
      cases hMem
      next hEq =>
        simp only [hEq, st.pog.toPropForm_addDisj _ _ _ _ hPog, PropForm.vars]
        exact Finset.union_subset (pfs.pog_vars' l₁ hL₁) (pfs.pog_vars' l₂ hL₂)
      next hMem =>
        have hNe : x ≠ y := fun h => absurd hMem (h ▸ hX)
        rw [st.pog.toPropForm_addDisj_of_ne _ _ _ _ _ hPog hNe]
        exact pfs.pog_vars y hMem
    partitioned := by
      intro y
      by_cases hEq : x = y
      . rw [st.pog.toPropForm_addDisj _ _ _ _ (hEq ▸ hPog)]
        refine addDisj_partitioned st.pogDefsTerm (LitVar.toPropFun l₁) (LitVar.toPropFun l₂) _ _ ?_
          pfs.uep_pogDefsTerm hDisjoint (pfs.equivalent_lits' l₁ hL₁) (pfs.equivalent_lits' l₂ hL₂)
          (pfs.partitioned' l₁) (pfs.partitioned' l₂)
        simp [hL₂]
      . rw [st.pog.toPropForm_addDisj_of_ne _ _ _ _ _ hPog hEq]
        exact pfs.partitioned y
    equivalent_clauseDb
    extends_pogDefsTerm
    uep_pogDefsTerm
    equivalent_lits
  }
  set (σ := State) ⟨st', pfs'⟩

def setRoot (r : ILit) : CheckerM Unit := do
  modify fun ⟨st, pfs⟩ => ⟨{ st with root := some r }, { pfs with }⟩

def checkFinalClauses (r : ILit) (st : PreState) : Except CheckerError { _u : Unit //
    (∀ idx C, st.clauseDb.getClause idx = some C → idx ∈ st.pogDefs' ∨ C = #[r])
    ∧ (∃ idxᵣ, st.clauseDb.getClause idxᵣ = some #[r]) } := do
  /- NOTE: This check is seriously inefficient. First, `all`/`any` don't use early return. Second,
  we loop over the clauses twice. Third, this could likely all be implemented in O(1) by storing
  the number `nClauses` of clauses. As long as `nClauses = st.pogDefs.size + 1` (`+ 1` for the root
  literal), the conclusion should follow from appropriate invariants. -/
  match h₁ : st.clauseDb.all (fun idx C => C = #[r] ∨ st.pogDefs.contains idx) with
  | true =>
    match h₂ : st.clauseDb.any (fun _ C => C = #[r]) with
    | true =>
      have hA := by
        intro idx C hGet
        have := st.clauseDb.all_true _ h₁ idx C hGet
        simp at this
        rw [PreState.pogDefs', HashSet.mem_toFinset]
        exact Or.comm.mp this
      have hE := by
        have ⟨idxᵣ, C, hGet, hP⟩ := st.clauseDb.any_true _ h₂
        simp at hP
        exact ⟨idxᵣ, hP ▸ hGet⟩
      return ⟨(), hA, hE⟩
    | false => throw <| .finalRootNotUnit r
  | false => throw <| .finalClausesInvalid

def checkFinalState : CheckerM { p : ICnf × Pog × ILit //
    p.1.toPropFun = ⟦p.2.1.toPropForm p.2.2⟧ } := do
  let ⟨st, pfs⟩ ← get

  let some r := st.root
    | throw <| .finalRootNotSet
  let ⟨_, hR, _⟩ ← getDeps st pfs r

  let ⟨_, hA, hE⟩ ← checkFinalClauses r st
  have : st.clauseDb.toPropFun = LitVar.toPropFun r ⊓ st.pogDefsTerm := by
    have ⟨idxᵣ, hGet⟩ := hE
    ext τ
    rw [st.clauseDb.satisfies_toPropFun, PreState.pogDefsTerm, satisfies_conj,
      st.clauseDb.satisfies_toPropFunSub]
    constructor
    . intro h
      have := h _ _ hGet
      dsimp [Clause.toPropFun] at this
      aesop
    . intro ⟨h₁, h₂⟩ _ _ hGet
      cases hA _ _ hGet
      next hMem => exact h₂ _ hMem _ hGet
      next hEq =>
        rw [hEq]
        simp [Clause.toPropFun, h₁]

  have : st.inputCnf.toPropFun = ⟦st.pog.toPropForm r⟧ := by
    have := this ▸ pfs.equivalent_clauseDb
    have := this.trans (pfs.equivalent_lits' r hR)
    have hInputVars := PropForm.semVars_subset_vars st.inputCnf.toPropForm
    simp at hInputVars
    have hPogVars := subset_trans (PropForm.semVars_subset_vars _) (pfs.pog_vars' r hR)
    exact equivalentOver_semVars hInputVars hPogVars this

  return ⟨(st.inputCnf, st.pog, r), this⟩

def checkProofStep (step : CpogStep) : CheckerM Unit :=
  match step with
  | .addAt idx C hints => addAt idx C hints
  | .delAt idx hints => delAt idx hints
  | .prod idx x ls => addProd idx x ls
  | .sum idx x l₁ l₂ hints => addSum idx x l₁ l₂ hints
  | .root r => setRoot r

/-- Check a CPOG proof and throw if it is invalid. If `count = True`, also return the model count
of `cnf` over `nVars` variables. Otherwise return an unspecified number. -/
def checkProof (cnf : ICnf) (nVars : Nat) (pf : Array CpogStep) (count : Bool := False) :
    Except String Nat := do
  let mut st : State ← Except.mapError toString (initial cnf nVars)
  for step in pf do
    try
      (_, st) ← Except.mapError toString (checkProofStep step |>.run st)
    catch e =>
      throw <| s!"error on line '{step.toDimacs}':\n{e}"
  let ⟨(_, _, r), _⟩ ← Except.mapError toString (checkFinalState.run' st)
  if count then
    if r.polarity = true then
      return st.val.pog.count nVars r.var
    else
      return 2^nVars - st.val.pog.count nVars r.var
  else
    return 0

/-
-- LATER: re-add tracing

/-- Wraps a well-formed checker state with extra stuff for tracing and debugging it. -/
structure CheckerState' where
  core : CheckerState
  verbose : Bool := false
  trace : Array String := #[]

namespace CheckerState

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def withTraces (f : Array String → String) (x : CheckerM Unit) : CheckerM Unit := do
  if (← get).verbose then
    let prevTrace ← modifyGet fun st => (st.trace, { st with trace := #[] })
    try x
    finally
      modify fun st => { st with trace := prevTrace.push <| f st.trace }
  else
    x

def log_ (msg : Unit → String) : CheckerM Unit := do
  modify fun st =>
    if st.verbose then { st with trace := st.trace.push <| msg () }
    else st

syntax "log! " interpolatedStr(term) : term
macro_rules
  | `(log! $interpStr) => `(log_ fun _ => s!$interpStr)

end CheckerState
-/

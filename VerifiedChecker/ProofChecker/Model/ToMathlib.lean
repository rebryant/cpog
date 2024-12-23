/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Classes.BEq

import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Perm

import LeanSAT.Upstream.ToMathlib

/-! Std.Logic or Std.Bool? -/

@[simp] theorem Bool.bnot_eq_to_not_eq (a b : Bool) :
  ((!a) = b) = ¬(a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_bnot_to_not_eq (a b : Bool) :
  (a = (!b)) = ¬(a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true_to_eq (a b : Bool) :
  (a = true ↔ b = true) = (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false_to_eq (a b : Bool) :
  (a = false ↔ b = false) = (a = b) := by cases a <;> cases b <;> decide

/-! Std.Logic -/

theorem Bool.not_eq_true_iff_ne_true {b : Bool} : (!b) = true ↔ ¬(b = true) := by
  cases b <;> decide

theorem Bool.bne_iff_not_beq [BEq α] {a a' : α} : a != a' ↔ ¬(a == a') :=
  Bool.not_eq_true_iff_ne_true

theorem Bool.beq_or_bne [BEq α] (a a' : α) : a == a' ∨ a != a' :=
  by
    cases h : a == a'
    . apply Or.inr
      simp [bne_iff_not_beq, h]
    . exact Or.inl rfl

@[simp]
theorem Bool.bne_eq_false [BEq α] {a a' : α} : (a != a') = false ↔ a == a' := by
  dsimp [bne]
  cases (a == a') <;> simp

/-! Std.Classes.BEq -/

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by cases (beq_iff_eq _ _).mp h; exact h
  trans h₁ h₂ := by cases (beq_iff_eq _ _).mp h₁; cases (beq_iff_eq _ _).mp h₂; exact h₁

theorem bne_symm [BEq α] [PartialEquivBEq α] {a b : α} : a != b → b != a :=
  fun h => Bool.not_eq_true_iff_ne_true.mpr fun h' =>
    Bool.bne_iff_not_beq.mp h (PartialEquivBEq.symm h')

/-! Data.List.Extra or something -/

@[specialize]
def List.foldlDep {α : Type u} {β : Type v} : (l : List β) → (f : α → (b : β) → b ∈ l → α) →
    (init : α) → α
  | nil,      _, init => init
  | cons b l, f, init => foldlDep l (fun a b h => f a b (.tail _ h)) (f init b (.head l))

@[specialize]
def List.mapDep {α : Type u} {β : Type v} : (l : List α) → (f : (a : α) → a ∈ l → β) → List β
  | nil,      _ => []
  | cons a l, f => f a (.head l) :: mapDep l fun a h => f a (.tail _ h)

@[simp]
theorem List.map_mapDep {γ : Type u} : (l : List α) → (f : (a : α) → a ∈ l → β) → (g : β → γ) →
    (l.mapDep f).map g = l.mapDep (fun a h => g (f a h))
  | nil,      _, _ => rfl
  | cons a l, f, g => by
    -- https://www.youtube.com/watch?v=Hd2JgADY9d8
    simp [map, mapDep, map_mapDep]

/-! Data.List.Lemmas -/

namespace List

def eventuallyRec {motive : List α → Sort _} {l : List α} {i : Fin l.length} {x : α}
    (xl : l.get i = x)
    (base : ∀ tail, motive (x :: tail))
    (cons : ∀ head tail, motive tail → motive (head :: tail)) :
    motive l :=
  match l with
  | nil => nomatch i.is_lt
  | a :: as =>
    let ⟨i, i_lt⟩ := i
    if h : i = 0 then
      have : x = a := by
        cases h
        simpa using xl.symm
      this ▸ base _ -- `dcast motive` would be better
    else
      have : i - 1 < as.length :=
        Nat.sub_lt_right_of_lt_add (Nat.one_le_iff_ne_zero.mpr h) (by simpa using i_lt)
      have : as.get ⟨i - 1, this⟩ = x := by
        rw [show (⟨i, i_lt⟩ : Fin (a :: as).length) = ⟨(i - 1) + 1, Nat.succ_lt_succ this⟩ by
          ext; exact (Nat.succ_pred h).symm] at xl
        simpa using xl
      cons _ _ (eventuallyRec this base cons)

theorem eventuallyInduction {motive : List α → Prop} {x : α} {l : List α}
    (xl : x ∈ l)
    (base : ∀ tail, motive (x :: tail))
    (cons : ∀ head tail, motive tail → motive (head :: tail)) :
    motive l :=
  have ⟨_, li⟩ := List.get_of_mem xl
  eventuallyRec li base cons

theorem foldlEventuallyInduction {β : Sort _} {motive : β → Prop} {x : α} {l : List α}
    (xl : x ∈ l)
    (op : β → α → β) (b : β)
    (base : ∀ b, motive (op b x))
    (cons : ∀ b a, motive b → motive (op b a)) :
    motive (l.foldl op b) := by
  rw [← foldr_reverse]
  have xl : x ∈ l.reverse := by simp [xl]
  generalize l.reverse = k at xl
  induction k generalizing b with
  | nil => cases xl
  | cons a as ih =>
    rw [foldr]
    cases mem_cons.mp xl with
    | inl h => cases h; apply base
    | inr h => exact cons _ _ (ih _ h)

/-! drop -/

theorem drop_eq_cons_get (l : List α) (i : Nat) (h : i < l.length)
    : l.drop i = l.get ⟨i, h⟩ :: l.drop (i + 1) :=
  go i l h
where go : (i : Nat) → (l : List α) → (h : i < l.length) → l.drop i = l[i] :: l.drop (i + 1)
  | 0,   _::_,  _ => by simp
  | n+1, _::as, h => by
    have : n < length as := Nat.lt_of_succ_lt_succ h
    have ih := go n as this
    simp [ih]

theorem drop_ext (l₁ l₂ : List α) (j : Nat)
    : (∀ i ≥ j, l₁.get? i = l₂.get? i) → l₁.drop j = l₂.drop j := by
  intro H
  apply ext fun k => ?_
  rw [get?_drop, get?_drop]
  apply H _ (Nat.le_add_right _ _)

/-! find? -/

theorem find?_filter (l : List α) (p q : α → Bool) (h : ∀ a, p a → q a) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [filter, find?]
    split <;> split <;> simp [*] at *

theorem find?_filter' (l : List α) (p q : α → Bool) (h : ∀ a, p a → !q a) :
    (l.filter q).find? p = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [filter]
    split
    next _ hQ => rw [find?_cons_of_neg _ (fun hP => by aesop), ih]
    next => exact ih

-- theorem find?_eraseP (l : List α) (p q : α → Bool) (h : ∀ a, p a → !q a) :
--     (l.eraseP q).find? p = l.find? p := by
--   induction l with
--   | nil => rfl
--   | cons x xs ih =>
--     dsimp [filter, eraseP]
--     split
--     next _ hP => aesop
--     next _ hP =>
--       cases (q x : Bool) with -- `split_ifs` doesn't work on `bif`
--       | false => rw [cond_false, find?_cons_of_neg _ (by simp [hP]), ih]
--       | true => rw [cond_true]

/-! foldl -/

theorem foldl_cons_fn (l₁ l₂ : List α) :
    l₁.foldl (init := l₂) (fun acc x => x :: acc) = l₁.reverse ++ l₂ := by
  induction l₁ generalizing l₂ <;> simp [*]

theorem foldl_append_fn (l₁ : List α) (l₂ : List β) (f : α → List β) :
    l₁.foldl (init := l₂) (fun acc x => acc ++ f x) = l₂ ++ l₁.bind f := by
  induction l₁ generalizing l₂ <;> simp [*]

end List

/-! Data.Array.Lemmas -/

theorem Array.get_of_mem_data {as : Array α} {a : α} : a ∈ as.data → ∃ (i : Fin as.size), as[i] = a :=
  List.get_of_mem

theorem Array.get_mem_data (as : Array α) (i : Fin as.size) : as[i] ∈ as.data := by
  simp [getElem_mem_data]

/-! Data.List.Perm -/

namespace List

/-- The way Lean 4 computes the motive with `elab_as_elim` has changed
relative to the behaviour of `elab_as_eliminator` in Lean 3.
See
https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Potential.20elaboration.20bug.20with.20.60elabAsElim.60/near/299573172
for an explanation of the change made here relative to mathlib3.
-/
@[elab_as_elim]
theorem perm_induction_on'
    {P : (l₁ : List α) → (l₂ : List α) → l₁ ~ l₂ → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (nil : P [] [] .nil)
    (cons : ∀ x l₁ l₂, (h : l₁ ~ l₂) → P l₁ l₂ h → P (x :: l₁) (x :: l₂) (.cons x h))
    (swap : ∀ x y l₁ l₂, (h : l₁ ~ l₂) → P l₁ l₂ h →
      P (y :: x :: l₁) (x :: y :: l₂) (.trans (.swap x y _) (.cons _ (.cons _ h))))
    (trans : ∀ l₁ l₂ l₃, (h₁ : l₁ ~ l₂) → (h₂ : l₂ ~ l₃) → P l₁ l₂ h₁ → P l₂ l₃ h₂ →
      P l₁ l₃ (.trans h₁ h₂)) : P l₁ l₂ p :=
  have P_refl l : P l l (.refl l) :=
    List.recOn l nil fun x xs ih ↦ cons x xs xs (Perm.refl xs) ih
  Perm.recOn p nil cons (fun x y l ↦ swap x y l l (Perm.refl l) (P_refl l)) @trans

end List

/-! Maybe Data.List.Unique -/

namespace List

/-- There is at most one element satisfying `p` in `l`. -/
-- TODO Move the other `of_unique` lemmas to this formulation
-- and move `pairwise'` lemmas below to `unique`
def unique (p : α → Prop) (l : List α) : Prop :=
  l.Pairwise (p · → ¬p ·)

def unique_cons_of_true {x : α} {l : List α} {p : α → Prop} :
    (x :: l).unique p → p x → ∀ y ∈ l, ¬p y :=
  fun h hP _ hY => rel_of_pairwise_cons h hY hP

theorem unique.sublist {l₁ l₂ : List α} {p : α → Prop} : l₁ <+ l₂ → l₂.unique p → l₁.unique p :=
  Pairwise.sublist

example {x y : α} {p : α → Prop} : (p x → ¬p y) → (p y → ¬p x) :=
  fun h hY hX => h hX hY

def unique.perm {l₁ l₂ : List α} {p : α → Prop} : l₁ ~ l₂ → l₁.unique p → l₂.unique p :=
  fun h h₁ => h.pairwise h₁ fun H hB hA => H hA hB

theorem find?_eq_of_perm_of_unique {l₁ l₂ : List α} {p : α → Bool} :
    l₁ ~ l₂ → l₁.unique (p ·) → l₁.find? p = l₂.find? p := by
  intro h hUniq
  induction h using perm_induction_on' with
  | nil => rfl
  | cons x l₁ _ _ ih =>
    have := ih (hUniq.sublist (sublist_cons x l₁))
    simp [find?, this]
  | swap x y l₁ l₂ _ ih =>
    dsimp [find?]
    split <;> split <;> try rfl
    next hY _ hX =>
      have : ¬p x := unique_cons_of_true hUniq hY x (mem_cons_self _ _)
      contradiction
    next => exact ih <| hUniq.sublist <| sublist_of_cons_sublist <| sublist_cons y (x :: l₁)
  | trans l₁ l₂ l₃ h₁₂ _ h₁ h₂ =>
    simp [h₁ hUniq, h₂ (hUniq.perm h₁₂)]

/-- If there is at most one element with the property `p`, finding that one element is the same
as finding any. -/
theorem find?_eq_some_of_unique {l : List α} {a : α} {p : α → Bool}
    : l.Pairwise (p · → !p ·) → (l.find? p = some a ↔ (a ∈ l ∧ p a)) := by
  refine fun h => ⟨fun h' => ⟨find?_mem h', find?_some h'⟩, ?_⟩
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro ⟨hMem, hP⟩
    cases mem_cons.mp hMem with
    | inl hX => simp [find?, ← hX, hP]
    | inr hXs =>
      unfold find?
      cases hPX : (p x) with
      | false =>
        apply ih (Pairwise.sublist (sublist_cons x xs) h) ⟨hXs, hP⟩
      | true =>
        cases hP ▸ (pairwise_cons.mp h |>.left a hXs hPX)

/-- If there is at most one element with the property `p`, erasing one such element is the same
as filtering out all of them. -/
theorem eraseP_eq_filter_of_unique (l : List α) (p : α → Bool)
    : l.Pairwise (p · → !p ·) → l.eraseP p = l.filter (!p ·) := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    specialize ih (Pairwise.sublist (sublist_cons x xs) h)
    cases hP : p x with
    | true =>
      rw [pairwise_cons] at h
      have : ∀ a ∈ xs, !p a := fun a hA => h.left a hA hP
      simp [eraseP, filter, hP, filter_eq_self.mpr this]
    | false => simp [eraseP_cons, filter, hP, ih]

theorem replaceF_of_unique {a b : α} {l : List α} (f : α → Option α) :
    a ∈ l → f a = some b → l.Pairwise (fun a₁ a₂ => (f a₁).isSome → ¬(f a₂).isSome) →
    l.replaceF f ~ b :: l.eraseP (f · |>.isSome) := by
  intro hMem hF hPws
  induction l with
  | nil => cases hMem
  | cons x xs ih =>
    unfold replaceF eraseP
    cases mem_cons.mp hMem with
    | inl hMem => simp [← hMem, hF, Perm.refl]
    | inr hMem =>
      have : f x = none := by
        have .cons hPws _ := hPws
        exact Option.eq_none_iff_forall_not_mem.mpr fun b hB' =>
          hPws a hMem (hB' ▸ rfl) (hF ▸ rfl)
      simp only [this, Option.isSome_none, cond_false]
      have := ih hMem (hPws.sublist <| sublist_cons _ _)
      exact .trans (.cons x this) (.swap b x _)

end List

theorem List.foldl_of_comm (l : List α) (f : β → α → β) (init : β) :
    (∀ b, ∀ a₁ ∈ l, ∀ a₂ ∈ l, f (f b a₁) a₂ = f (f b a₂) a₁) →
    (x : α) → x ∈ l → ∃ b, l.foldl f init = f b x := by
  intro hComm x hX
  let fn : List α × β → α → List α × β := fun (accL, acc) a => (accL ++ [a], f acc a)
  have hEq : ∀ (p : List α × β), (l.foldl fn p).1 = p.1 ++ l ∧ (l.foldl fn p).2 = l.foldl f p.2 := by
    intro p
    clear hX
    induction' l with a as ih generalizing p
    . simp
    simp_all only [mem_cons, implies_true, forall_eq_or_imp,
      foldl_cons, append_assoc, singleton_append, and_self]
  have := List.foldlRecOn (l := l) (C := fun (accL, acc) => x ∈ accL → ∃ b, acc = f b x)
    (op := fn) (b := ([], init))
    (hb := by simp)
    (hl := by
      intro p ih a hA h
      cases' mem_append.mp h with h h
      . have ⟨b, hB⟩ := ih h
        use f b a
        rw [hB, hComm b a hA x hX]
      . use p.2
        simp [mem_singleton.mp h])
  simp_rw [(hEq _).1, (hEq _).2] at this
  apply this hX

/-! Loop -/

def loopM_with_invariant [Monad m] {State : Type _} (n : Nat)
    (invariant : Nat → State → Prop)
    (start_state : { st // invariant 0 st })
    (step : (i : Fin n) → { st // invariant i st } → m { st // invariant (i+1) st }) :
    m { st // invariant n st } :=
  go n 0 (by rw [add_zero]) start_state
where
  go : (b : Nat) → (i : Nat) → b + i = n → { st // invariant i st } → m { st // invariant n st }
    | 0, i, h, state =>
      have : i = n := Nat.zero_add i ▸ h
      return this ▸ state
    | (b + 1), i, h, state => do
      let v ← step ⟨i, by rw [← h]; linarith⟩ state
      go b (i + 1) (by rw [← h]; ac_rfl) v

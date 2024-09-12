/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Data.RBMap

import ProofChecker.Model.ToMathlib

namespace Std.RBSet

theorem mem_union [@TransCmp α cmp_] {s t : RBSet α cmp_} :
    v ∈ s.union t ↔ v ∈ s ∨ v ∈ t := by
  rw [union, foldl_eq_foldl_toList, t.mem_iff_mem_toList]
  induction toList t generalizing s with
  | nil => simp
  | cons t ts ih =>
    simp [ih, mem_insert, OrientedCmp.cmp_eq_eq_symm]
    tauto

theorem all_iff [LinearOrder α] {p : α → Bool} {s : RBSet α compare} :
    s.all p ↔ ∀ a ∈ s, p a := by
  rw [all, RBNode.all_iff, RBNode.All_def]
  simp_rw [← mem_toList, mem_iff_mem_toList]
  aesop (add norm compare_eq_iff_eq)

/-- Calculate the union of an array of `RBSet`s, and check if the array elements are all pairwise
disjoint. Return `(⋃ ss, true)` if array elements are pairwise disjoint, otherwise `(⋃ ss, false)`. -/
def disjointUnion (ss : Array (RBSet α cmp_)) : RBSet α cmp_ × Bool :=
  ss.foldl (init := (.empty, true)) fun (U, b) t =>
    let b := b && t.all (!U.contains ·)
    (U.union t, b)

theorem disjointUnion_characterization [LinearOrder α] (ss : Array (RBSet α compare)) :
    (∀ a, a ∈ (disjointUnion ss).fst ↔ ∃ s ∈ ss.data, a ∈ s)
    ∧ ((disjointUnion ss).snd →
      ∀ (i j : Fin ss.size), i ≠ j → ∀ a ∈ ss[i], a ∉ ss[j]) :=
  have ⟨h₁, h₂, h₃⟩ := ss.foldl_induction
    (motive := fun i (acc : RBSet α compare × Bool) =>
      (∀ a ∈ acc.1, ∃ s ∈ ss.data, a ∈ s) ∧
      (∀ (j : Fin ss.size), j < i → ∀ a ∈ ss[j], a ∈ acc.1) ∧
      (acc.2 → ∀ (j k : Fin ss.size), j < i → k < i → j ≠ k → ∀ a ∈ ss[j], a ∉ ss[k]))
    (init := (.empty, true)) (h0 := by simp; intro a h; exact h.elim)
    (f := fun (U, b) t =>
      let b := b && t.all (!U.contains ·)
      (U.union t, b))
    (hf := by
      intro i (U, b) ⟨ih₁, ih₂, ih₃⟩
      simp only [mem_union]
      refine ⟨?step₁, ?step₂, ?step₃⟩
      case step₁ =>
        intro a hMem
        cases hMem with
        | inl h =>
          exact ih₁ a h
        | inr h =>
          exact ⟨ss[i], Array.get_mem_data ss i, h⟩
      case step₂ =>
        intro j hJ
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJ) with
        | inl h =>
          have := ih₂ j h
          tauto
        | inr h =>
          simp [h]
          tauto
      case step₃ =>
        intro hB j k hJ hK hNe
        simp only [Bool.and_eq_true, all_iff,
          getElem_fin, Bool.bnot_eq_to_not_eq, contains_iff] at hB
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJ) <;>
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hK)
        case inl.inl hJ hK =>
          exact ih₃ hB.left j k hJ hK hNe
        case inr.inr hJ hK =>
          have := hJ.trans hK.symm
          exact absurd (Fin.eq_of_val_eq this) hNe
        case inl.inr hJ hK =>
          intro a hAJ hAK
          have hAU := ih₂ _ hJ a hAJ
          simp only [hK, getElem_fin] at hAK
          apply hB.right a hAK hAU
        case inr.inl hJ hK =>
          intro a hAJ hAK
          simp only [hJ, getElem_fin] at hAJ
          apply hB.right a hAJ
          exact ih₂ k hK _ hAK)
  by
    dsimp [disjointUnion]
    refine ⟨fun a => ⟨fun hMem => h₁ a hMem, ?_⟩,
      fun h i j hNe => h₃ h i j i.isLt j.isLt hNe⟩
    intro ⟨s, hS, hA⟩
    have ⟨i, hI⟩ := Array.get_of_mem_data hS
    apply h₂ i i.isLt _ (hI ▸ hA)

theorem mem_disjointUnion [LinearOrder α] (ss : Array (RBSet α compare)) (a : α) :
    a ∈ (disjointUnion ss).fst ↔ ∃ s ∈ ss.data, a ∈ s :=
  disjointUnion_characterization ss |>.left a

theorem disjoint_disjointUnion [LinearOrder α] (ss : Array (RBSet α compare)) : (disjointUnion ss).snd →
    ∀ (i j : Nat) (hI : i < ss.size) (hJ : j < ss.size), i ≠ j → ∀ a ∈ ss[i], a ∉ ss[j] :=
  fun h i j hI hJ hNe =>
    disjointUnion_characterization ss |>.right h ⟨i, hI⟩ ⟨j, hJ⟩ (by simp [hNe])

end Std.RBSet

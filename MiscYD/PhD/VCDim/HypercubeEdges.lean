/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Partition.Finpartition
public import MiscYD.Mathlib.Combinatorics.SetFamily.Shatter

/-!
# A small VC dimension family has few edges in the L¹ metric

This file proves that set families over a finite type that have small VC dimension have a number
of pairs `(A, B)` with `#(A ∆ B) = 1` linear in their size.

## References

* *Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded
  Vapnik-Chervonenkis Dimension*, David Haussler
* Write-up by Thomas Bloom: http://www.thomasbloom.org/notes/vc.html
-/

public section

open Finset
open scoped symmDiff

namespace SetFamily
variable {α : Type*} {𝓕 𝓒 : Finset (Set α)} {A B : Set α} {d : ℕ}

/-- The edges of the subgraph of the hypercube `Set α` induced by a finite set of vertices
`𝓕 : Finset (Set α)`. -/
noncomputable def hypercubeEdgeFinset (𝓕 : Finset (Set α)) : Finset (Set α × Set α) :=
  {AB ∈ 𝓕 ×ˢ 𝓕 | (AB.1 ∆ AB.2).ncard = 1}

@[simp] lemma prodMk_mem_hypercubeEdgeFinset :
    (A, B) ∈ hypercubeEdgeFinset 𝓕 ↔ A ∈ 𝓕 ∧ B ∈ 𝓕 ∧ (A ∆ B).ncard = 1 := by
  simp [hypercubeEdgeFinset, and_assoc]

open scoped Classical in
@[simp]
private lemma filter_finite_symmDiff_inj (hB : B ∈ 𝓕) :
    {C ∈ 𝓕 | (A ∆ C).Finite} = {C ∈ 𝓕 | (B ∆ C).Finite} ↔ (A ∆ B).Finite where
  mp hAB := by
    have : B ∈ {C ∈ 𝓕 | (A ∆ C).Finite} := hAB ▸ mem_filter.2 ⟨hB, by simp⟩
    exact (mem_filter.1 this).2
  mpr hAB := by ext D; simp [hAB.symmDiff_congr]

open scoped Classical in
/-- Partition a set family into its components of finite symmetric difference. -/
noncomputable def finiteSymmDiffFinpartition (𝓕 : Finset (Set α)) : Finpartition 𝓕 where
  parts := 𝓕.image fun A ↦ {B ∈ 𝓕 | (A ∆ B).Finite}
  supIndep := by
    simp +contextual only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise,
      coe_image, Set.mem_image, mem_coe, ne_eq, Function.onFun, id, disjoint_left,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, forall_const,
      filter_finite_symmDiff_inj]
    refine fun A hA B hB hAB C hC hAC hBC ↦ hAB ?_
    exact (hAC.union <| symmDiff_comm B C ▸ hBC).subset <| symmDiff_triangle ..
  sup_parts := by
    simp only [sup_image, le_antisymm_iff, Finset.sup_le_iff, le_eq_subset,
      filter_subset, implies_true, true_and, Function.id_comp]
    exact fun A hA ↦ mem_sup.2 ⟨A, hA, mem_filter.2 ⟨hA, by simp⟩⟩
  bot_notMem := by
    simp only [bot_eq_empty, mem_image, filter_eq_empty_iff, not_exists, not_and, not_forall,
      Decidable.not_not]
    exact fun A hA ↦ ⟨A, hA, by simp⟩

open scoped Classical in
lemma finite_symmDiff_of_mem_finiteSymmDiffFinpartition
    (h𝓒 : 𝓒 ∈ (finiteSymmDiffFinpartition 𝓕).parts) (hA : A ∈ 𝓒) (hB : B ∈ 𝓒) :
    (A ∆ B).Finite := by
  simp only [finiteSymmDiffFinpartition, mem_image] at h𝓒
  obtain ⟨C, hC, rfl⟩ := h𝓒
  rw [mem_filter] at hA hB
  exact ((symmDiff_comm A C ▸ hA.2).union hB.2).subset <| symmDiff_triangle ..

open scoped Classical in
lemma finite_iUnion_sdiff_iInter_of_mem_finiteSymmDiffFinpartition
    (h𝓒 : 𝓒 ∈ (finiteSymmDiffFinpartition 𝓕).parts) : ((⋃ A ∈ 𝓒, A) \ ⋂ A ∈ 𝓒, A).Finite := by
  simp_rw [Set.iUnion_diff, Set.diff_iInter]
  exact .biUnion 𝓒.finite_toSet fun A hA ↦ .biUnion 𝓒.finite_toSet fun B hB ↦
    (finite_symmDiff_of_mem_finiteSymmDiffFinpartition h𝓒 hA hB).subset le_sup_left

open scoped Classical in
@[simp]
lemma sup_finiteSymmDiffFinpartition_hypercubeEdgeFinset (𝓕 : Finset (Set α)) :
    (finiteSymmDiffFinpartition 𝓕).parts.sup hypercubeEdgeFinset = hypercubeEdgeFinset 𝓕 := by
  ext ⟨A, B⟩
  simp only [finiteSymmDiffFinpartition, sup_image, mem_sup, Function.comp_apply,
    prodMk_mem_hypercubeEdgeFinset, mem_filter, and_assoc, and_left_comm, exists_and_left,
    and_congr_right_iff, Set.ncard_eq_one]
  refine fun hA hB ↦ ⟨?_, ?_⟩
  · rintro ⟨C, hC, hCA, hCB, hAB⟩
    exact hAB
  · rintro ⟨a, ha⟩
    exact ⟨A, by simp [*]⟩

open scoped Classical Set.Notation in
/-- Restrict a component of finite symmetric difference to a set family over a finite type. -/
noncomputable def restrictFiniteSymmDiffComponent (𝓒 : Finset (Set α)) :
    Finset (Set ↥((⋃ A ∈ 𝓒, A) \ ⋂ A ∈ 𝓒, A)) :=
  𝓒.image fun A ↦ _ ↓∩ A ∆ ⋂ B ∈ 𝓒, B

@[simp] lemma card_restrictFiniteSymmDiffComponent (𝓒 : Finset (Set α)) :
    #(restrictFiniteSymmDiffComponent 𝓒) = #𝓒 := by
  classical
  refine card_image_of_injOn fun A hA B hB hAB ↦ ?_
  replace hAB := congr(Subtype.val '' $hAB)
  have : (⋃ A ∈ 𝓒, A) ∆ ⋂ B ∈ 𝓒, B = ((⋃ A ∈ 𝓒, A) \ ⋂ B ∈ 𝓒, B) :=
    symmDiff_of_ge <| Set.biInter_subset_biUnion ⟨A, hA⟩
  stop
  simp_rw [Set.image_preimage_eq_inter_range, Subtype.range_val, ← this,
    ← Set.inter_symmDiff_distrib_left, Set.inter_sdiff_left_comm _ (⋃ _, _)] at hAB

protected lemma _root_.IsNIPWith.restrictFiniteSymmDiffComponent
    (h𝓒 : IsNIPWith d (𝓒 : Set (Set α))) :
    IsNIPWith d (restrictFiniteSymmDiffComponent 𝓒 : Set (Set ↑((⋃ A ∈ 𝓒, A) \ ⋂ A ∈ 𝓒, A))) :=
  sorry

private lemma _root_.IsNIPWith.card_hypercubeEdgeFinset_le_of_finite [Finite α]
    (h𝓕 : IsNIPWith d (𝓕 : Set (Set α))) : #(hypercubeEdgeFinset 𝓕) ≤ d * #𝓕 := by
  sorry

lemma IsNIPWith.card_hypercubeEdgeFinset_le (h𝓕 : IsNIPWith d (𝓕 : Set (Set α))) :
    #(hypercubeEdgeFinset 𝓕) ≤ d * #𝓕 := by
  classical
  calc
    #(hypercubeEdgeFinset 𝓕)
    _ = ∑ 𝓒 ∈ (finiteSymmDiffFinpartition 𝓕).parts, #(hypercubeEdgeFinset 𝓒) := by
      rw [← sup_finiteSymmDiffFinpartition_hypercubeEdgeFinset, sup_eq_biUnion, card_biUnion]
      simp +contextual only [finiteSymmDiffFinpartition, mem_image, ne_eq, hypercubeEdgeFinset,
        disjoint_left, mem_filter, mem_product, and_true, not_and, and_imp,
        forall_exists_index, Prod.forall, forall_apply_eq_imp_iff₂, forall_const,
        filter_finite_symmDiff_inj, Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe]
      refine fun A hA B hB hAB C D hC hAC hD hAD hCD hBC hBD ↦ hAB ?_
      exact (hAC.union <| symmDiff_comm B C ▸ hBC).subset <| symmDiff_triangle ..
    _ ≤ ∑ 𝓒 ∈ (finiteSymmDiffFinpartition 𝓕).parts, d * #𝓒 := by
      gcongr with 𝓒 h𝓒
      have : Finite ↥((⋃ A ∈ 𝓒, A) \ ⋂ A ∈ 𝓒, A) :=
        finite_iUnion_sdiff_iInter_of_mem_finiteSymmDiffFinpartition h𝓒
      calc
        #(hypercubeEdgeFinset 𝓒)
        _ = #(hypercubeEdgeFinset (restrictFiniteSymmDiffComponent 𝓒)) := sorry
        _ ≤ d * #(restrictFiniteSymmDiffComponent 𝓒) := by
          refine (h𝓕.anti ?_).restrictFiniteSymmDiffComponent.card_hypercubeEdgeFinset_le_of_finite
          gcongr
          exact mod_cast (finiteSymmDiffFinpartition 𝓕).le h𝓒
        _ = d * #𝓒 := by rw [card_restrictFiniteSymmDiffComponent]
    _  = d * #𝓕 := by
      rw [← mul_sum, ← card_biUnion, ← sup_eq_biUnion]
      · erw [(finiteSymmDiffFinpartition 𝓕).sup_parts]
      · exact supIndep_iff_pairwiseDisjoint.1 (finiteSymmDiffFinpartition 𝓕).supIndep

end SetFamily

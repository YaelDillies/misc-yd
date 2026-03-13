module

public import Mathlib.Analysis.Convex.Combination

public section

open AffineMap Finset

section oldVars
variable {ι R E : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup E]
  [Module R E] {s : Finset ι} {f : ι → E} {x : E}

lemma mem_convexHull_image :
    x ∈ convexHull R (f '' s) ↔
      ∃ w : ι → R, (∀ i ∈ s, 0 ≤ w i) ∧ ∑ i ∈ s, w i = 1 ∧ s.centerMass w f = x where
  mp hp := by
    classical
    rw [← Subtype.range_val (α := ι) (s := s), ← Set.range_comp,
      convexHull_range_eq_exists_affineCombination] at hp
    obtain ⟨t, w, hw₀, hw₁, rfl⟩ := hp
    refine ⟨fun i ↦ if hi : i ∈ Subtype.val '' (t : Set s) then w ⟨i, by aesop⟩ else 0,
      by aesop, ?_⟩
    · simp [Finset.sum_dite]
      sorry
  mpr := by
    rintro ⟨w, hw₀, hw₁, rfl⟩; exact s.centerMass_mem_convexHull hw₀ (by simp [hw₁]) (by aesop)

end oldVars

variable {ι 𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {s t : Finset ι} {v w : ι → 𝕜} {x y : ι → V} {i : ι}

@[congr]
lemma centerMass_congr (hst : s = t) (hvw : ∀ i ∈ t, v i = w i) (hxy : ∀ i ∈ t, x i = y i) :
    s.centerMass v x = t.centerMass w y := by
  unfold centerMass; rw [sum_congr hst hvw, sum_congr hst fun i hi ↦ by rw [hvw i hi, hxy i hi]]

variable [DecidableEq ι]

lemma centerMass_union (hst : Disjoint s t) (hs : (∀ i ∈ s, w i = 0) ∨ ∑ i ∈ s, w i ≠ 0)
    (ht : (∀ i ∈ t, w i = 0) ∨ ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x := by
  obtain hs | hs := hs
  · simp only [sum_union hst, sum_eq_zero hs, zero_add] at hw₁
    simp only [centerMass, sum_union hst, sum_eq_zero hs, hw₁, zero_add, inv_one, smul_add,
      one_smul, inv_zero, zero_smul, smul_zero, add_eq_right]
    exact sum_eq_zero fun i hi ↦ by simp [hs _ hi]
  obtain ht | ht := ht
  · simp only [sum_union hst, sum_eq_zero ht, add_zero] at hw₁
    simp only [centerMass, sum_union hst, hw₁, sum_eq_zero ht, add_zero, inv_one, smul_add,
      one_smul, inv_zero, zero_smul, smul_zero, add_eq_left]
    exact sum_eq_zero fun i hi ↦ by simp [ht _ hi]
  · simp [centerMass, hs, ht, hst, sum_union, hw₁]

lemma centerMass_union_of_ne_zero (hst : Disjoint s t) (hs : ∑ i ∈ s, w i ≠ 0)
    (ht : ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x :=
  centerMass_union hst (.inr hs) (.inr ht) hw₁

lemma lineMap_centerMass_centerMass (hst : Disjoint s t)
    (hs : (∀ i ∈ s, w i = 0) ∨ ∑ i ∈ s, w i ≠ 0) (ht : (∀ i ∈ t, w i = 0) ∨ ∑ i ∈ t, w i ≠ 0)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x := by
  rw [lineMap_apply_module, ← hw₁, sum_union hst, add_sub_cancel_right,
    centerMass_union hst hs ht hw₁]

lemma lineMap_centerMass_centerMass_of_ne_zero (hst : Disjoint s t) (hs : ∑ i ∈ s, w i ≠ 0)
    (ht : ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x :=
  lineMap_centerMass_centerMass hst (.inr hs) (.inr ht) hw₁

lemma lineMap_centerMass_sdiff (hi : i ∈ s) (hi₀ : w i ≠ 0) (hi₁ : w i ≠ 1)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  rw [← centerMass_singleton i x hi₀, ← sum_singleton w i,
    lineMap_centerMass_centerMass] <;>
    simp [*, sub_eq_zero, eq_comm (b := w _)]

lemma centerMass_sdiff_of_weight_eq_zero (hi : i ∈ s) (hi₀ : w i = 0) :
    (s \ {i}).centerMass w x = s.centerMass w x := by
  simp [hi₀, sum_sdiff_eq_sub (singleton_subset_iff.2 hi), centerMass]

lemma lineMap_centerMass_sdiff_singleton_of_ne_one (hi : i ∈ s) (hi₁ : w i ≠ 1)
    (hw₁ : ∑ j ∈ s, w j = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  obtain hi₀ | hi₀ := eq_or_ne (w i) 0
  · simp [centerMass_sdiff_of_weight_eq_zero hi, hi₀]
  · rw [← centerMass_singleton i x hi₀, ← sum_singleton w i, lineMap_centerMass_centerMass] <;>
      simp [*, sub_eq_zero, eq_comm (b := w _)]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma centerMass_union_of_nonneg (hst : Disjoint s t) (hw₀ : ∀ i ∈ s ∪ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x := by
  refine centerMass_union hst ?_ ?_ hw₁
  · rw [← sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| subset_union_left hj]
    exact em _
  · rw [← sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| subset_union_right hj]
    exact em _

lemma lineMap_centerMass_centerMass_of_nonneg (hst : Disjoint s t) (hw₀ : ∀ i ∈ s ∪ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x := by
  rw [lineMap_apply_module, ← hw₁, sum_union hst, add_sub_cancel_right,
    centerMass_union_of_nonneg hst hw₀ hw₁]

lemma lineMap_centerMass_sdiff_singleton_of_nonneg (hi : i ∈ s) (hw₀ : ∀ j ∈ s \ {i}, 0 ≤ w j)
    (hw₁ : ∑ j ∈ s, w j = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  obtain hi₁ | hi₁ := eq_or_ne (w i) 1
  · rw [← centerMass_singleton i x (w := w) (by simp [hi₁]), ← sum_singleton w i,
      lineMap_centerMass_centerMass]
    rotate_left 2
    · rw [← sum_eq_zero_iff_of_nonneg hw₀]
      exact em _
    all_goals simp [*]
  · exact lineMap_centerMass_sdiff_singleton_of_ne_one hi hi₁ hw₁

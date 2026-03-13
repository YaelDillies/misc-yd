/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Finset.Sups
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic

/-!
# Positive difference

This file defines the positive difference of set families and sets in an ordered additive group.

## Main declarations

* `Finset.posDiffs`: Positive difference of set families.
* `Finset.posSub`: Positive difference of sets in an ordered additive group.

## Notations

We declare the following notation in the `finset_family` locale:
* `s \₊ t` for `finset.posDiffs s t`
* `s -₊ t` for `finset.posSub s t`

## References

* [Bollobás, Leader, Radcliffe, *Reverse Kleitman Inequalities][bollobasleaderradcliffe1989]
-/

public section

open scoped Pointwise

variable {α : Type*}

namespace Finset

/-! ### Positive set difference -/

section posDiffs
section GeneralizedBooleanAlgebra
variable [GeneralizedBooleanAlgebra α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α]
  {s t : Finset α} {a : α}

/-- The positive set difference of finsets `s` and `t` is the set of `a \ b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posDiffs (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a \ b

scoped[FinsetFamily] infixl:70 " \\₊ " => Finset.posDiffs

open scoped FinsetFamily

@[simp] lemma mem_posDiffs : a ∈ s \₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b \ c = a := by
  simp_rw [posDiffs, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

@[simp] lemma posDiffs_empty (s : Finset α) : s \₊ ∅ = ∅ := by simp [posDiffs]
@[simp] lemma empty_posDiffs (s : Finset α) : ∅ \₊ s = ∅ := by simp [posDiffs]

lemma posDiffs_subset_diffs : s \₊ t ⊆ s \\ t := by
  simp only [subset_iff, mem_posDiffs, mem_diffs]
  exact fun a ⟨b, hb, c, hc, _, ha⟩ ↦ ⟨b, hb, c, hc, ha⟩

end GeneralizedBooleanAlgebra

open scoped FinsetFamily

section Finset

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

lemma card_posDiffs_self_le (h𝒜 : (𝒜 : Set (Finset α)).OrdConnected) :
    #(𝒜 \₊ 𝒜) ≤ #𝒜 := by
  revert h𝒜
  refine Finset.memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · intro
    rfl
  · rintro a 𝒜 h𝒜₀ h𝒜₁ h𝒜
    sorry

/-- A **reverse Kleitman inequality**. -/
lemma le_card_upper_inter_lower (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) : #(𝒜 \₊ ℬ) ≤ #(𝒜 ∩ ℬ) := by
  refine (card_le_card ?_).trans (card_posDiffs_self_le ?_)
  · simp_rw [subset_iff, mem_posDiffs, mem_inter]
    rintro _ ⟨s, hs, t, ht, hts, rfl⟩
    exact ⟨s, ⟨hs, hℬ hts ht⟩, t, ⟨h𝒜 hts hs, ht⟩, hts, rfl⟩
  · rw [coe_inter]
    exact h𝒜.ordConnected.inter hℬ.ordConnected

end Finset
end posDiffs

/-! ### Positive subtraction -/

section posSub
variable [Sub α] [Preorder α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α] {s t : Finset α}
  {a : α}

/-- The positive subtraction of finsets `s` and `t` is the set of `a - b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posSub (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a - b

scoped[FinsetFamily] infixl:70 " -₊ " => Finset.posSub

open scoped FinsetFamily

lemma mem_posSub : a ∈ s -₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b - c = a := by
  simp_rw [posSub, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

lemma posSub_subset_sub : s -₊ t ⊆ s - t := fun x ↦ by
  rw [mem_posSub, mem_sub]; exact fun ⟨b, hb, c, hc, _, h⟩ ↦ ⟨b, hb, c, hc, h⟩

lemma card_posSub_self_le (hs : (s : Set α).OrdConnected) : #(s -₊ s) ≤ #s := sorry

end posSub
end Finset

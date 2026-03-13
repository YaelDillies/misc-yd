module

public import Mathlib.Combinatorics.SetFamily.Shatter

public section

variable {α : Type*}

section SemilatticeInf
variable [SemilatticeInf α] {𝒜 ℬ : Set α} {A B : α}

/-- A set family `𝒜` shatters a set `A` if all subsets of `A` can be obtained as the intersection
of `A` with some element of the set family. We also say that `A` is *traced* by `𝒜`. -/
def Shatters (𝒜 : Set α) (A : α) : Prop := ∀ ⦃B⦄, B ≤ A → ∃ C ∈ 𝒜, A ⊓ C = B

lemma Shatters.mono (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hB ↦ let ⟨C, hC, hCB⟩ := h𝒜 hB; ⟨C, h hC, hCB⟩

lemma Shatters.anti (h : A ≤ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := fun C hC ↦ by
  obtain ⟨D, hD, rfl⟩ := hB (hC.trans h); exact ⟨D, hD, inf_congr_right hC <| inf_le_of_left_le h⟩

end SemilatticeInf

section Set
variable {d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)}

open scoped Finset

/-- A set family `𝒜` is `d`-NIP if it has VC dimension at most `d`, namely if all the sets it
shatters have size at most `d`. -/
def IsNIPWith (d : ℕ) (𝒜 : Set (Set α)) : Prop := ∀ ⦃A : Finset α⦄, Shatters 𝒜 A → #A ≤ d

lemma IsNIPWith.anti (hℬ𝒜 : ℬ ⊆ 𝒜) (h𝒜 : IsNIPWith d 𝒜) : IsNIPWith d ℬ :=
  fun _A hA ↦ h𝒜 <| hA.mono hℬ𝒜

lemma IsNIPWith.mono (hd : d₁ ≤ d₂) (hd₁ : IsNIPWith d₁ 𝒜) : IsNIPWith d₂ 𝒜 :=
  fun _A hA ↦ (hd₁ hA).trans hd

end Set

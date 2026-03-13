/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import MiscYD.Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Haussler's packing lemma

This file proves Haussler's packing lemma, which is the statement that an `ε`-separated set family
of VC dimension at most `d` over finitely many elements has size at most `(Cε⁻¹) ^ d` for some
absolute constant `C`.

## References

* *Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded
  Vapnik-Chervonenkis Dimension*, David Haussler
* Write-up by Thomas Bloom: http://www.thomasbloom.org/notes/vc.html
-/

public section

open Fintype Metric Real
open scoped Finset NNReal

namespace SetFamily
variable {α : Type*} [Fintype α] {𝓕 : Finset (Set α)} {k d : ℕ}

/-- The **Haussler packing lemma** -/
theorem haussler_packing (isNIPWith_𝓕 : IsNIPWith d (𝓕 : Set (Set α)))
    (isSeparated_𝓕 : IsSeparated (k / card α)
      ((fun A : Set α ↦ WithLp.toLp 1 (A.indicator (1 : α → ℝ))) '' 𝓕))
    (hk : k ≤ card α) : #𝓕 ≤ exp 1 * (d + 1) * (2 * exp 1 * (card α + 1) / (k + 2 * d + 2)) :=
  sorry

end SetFamily

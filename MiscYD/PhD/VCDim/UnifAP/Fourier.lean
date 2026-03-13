/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import MiscYD.PhD.VCDim.UnifAP.Defs

/-!
# Fourier analysis of uniformly almost periodic functions
-/

public section

open Filter
open scoped Topology

variable {Λ : ℝ} {f : ℝ → ℂ}

variable (f) in
/-- The **mean** of an uniformly almost periodic function `f` is the limit of its average on
`[0, X]` as `X → +∞`. -/
noncomputable def mean : ℂ := limUnder atTop fun X ↦ ⨍ x in (0)..X, f x

lemma IsUnifAlmostPeriodic.tendsto_mean (hf : IsUnifAlmostPeriodic f) :
    Tendsto (fun X ↦ ⨍ x in (0)..X, f x) atTop (𝓝 (mean f)) := sorry

variable (Λ f) in
/-- The **Fourier coefficient** at `Λ` of an uniformly almost periodic function `f` is the mean of
`x ↦ f x * exp (-iΛx)`. -/
noncomputable def meanFourierCoeff : ℂ := mean fun x ↦ f x * .exp (-.I * Λ * x)

/-- The **Fourier exponents** of an uniformly almost periodic function `f` are at most countable. -/
lemma IsUnifAlmostPeriodic.countable_meanFourierCoeff_ne_zero :
    {Λ | meanFourierCoeff Λ f ≠ 0}.Countable := sorry

/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
#  Riesz–Markov–Kakutani representation theorem for `NNReal`

This file proves the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `NNReal`-linear functionals `Λ`.

## Implementation notes

The proof depends on the version of the theorem for `Real`-linear functional Λ because in a standard
proof one has to prove the inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.
Here we prove the result by writing `ℝ≥0`-linear `Λ` in terms of `ℝ`-linear `toRealLinear Λ` and by
reducing the statement to the `ℝ`-version of the theorem.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

namespace NNRealRMK

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (lower) Lebesgue integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal
to `Λ f`. -/
theorem lintegral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
  rw [lintegral_coe_eq_integral, ← ENNReal.ofNNReal_toNNReal]
  · simp only [ENNReal.coe_inj]
    rw [Real.toNNReal_of_nonneg (by apply integral_nonneg; intro x; simp),
      ← NNReal.coe_inj, ← eq_toRealLinear_toReal Λ f,
      ← RealRMK.integral_rieszMeasure (@nonneg_toRealLinear _ _ Λ) f.toReal]
    simp only [toReal_apply, NNReal.coe_mk]
    congr
    exact Eq.symm (eq_toNNRealLinear_toRealLinear Λ)
  rw [rieszMeasure]
  exact Continuous.integrable_of_hasCompactSupport (by continuity)
    (HasCompactSupport.comp_left f.hasCompactSupport rfl)

end NNRealRMK

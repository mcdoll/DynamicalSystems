/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability

/-! # Stability of a scalar multiplication map -/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α 𝕜 E F : Type*}

variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace α]
  [Bornology α] {s : ι → Set α} {μ : Measure α}

/-- The multiplication operator with an almost everywhere bounded function is `Lp` finite gain
stable. -/
theorem smul_isFiniteGainStableWith {f : α → 𝕜} (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ) {k : ℝ}
    (h_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ k) :
    (fun (u : α → E) (x : α) ↦ (f x) • (u x)).IsFiniteGainStableWith k.toNNReal 0 s p μ := by
  constructor
  · intro u hu s hs
    apply (hu s hs).smul (p := ∞)
    apply memLp_top_of_bound hf.restrict k
    exact h_bound.filter_mono ae_restrict_le
  · intro t u hu
    calc
      _ ≤ ENNReal.ofReal k * eLpNorm u p (μ.restrict (s t)) := by
        apply MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        filter_upwards [h_bound.filter_mono ae_restrict_le] with x hbdd
        grw [norm_smul, hbdd]
      _ = _ := by
        simp only [ENNReal.coe_zero, add_zero]
        rfl

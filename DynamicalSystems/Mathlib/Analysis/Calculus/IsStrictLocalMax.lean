/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral

/-! # Existence -/

variable {E F : Type*}

open scoped NNReal Nat

variable {a b : ℝ≥0}

theorem NNReal.exists_pos_mul_lt (hb : b ≠ 0) : ∃ c > 0, c * a < b := by
  by_cases! h : a ≠ 0
  · use b / (2 * a), by positivity
    field_simp
    exact one_lt_two
  · simp only [gt_iff_lt, h, mul_zero, exists_and_right]
    exact ⟨⟨1, zero_lt_one⟩, hb.pos⟩

theorem Real.exists_pos_mul_lt {a b : ℝ} (hb : 0 < b) : ∃ c > 0, c * a < b := by
  obtain ⟨c, hc, h⟩ := NNReal.exists_pos_mul_lt (a := a.toNNReal) (b := b.toNNReal) (by simp [hb])
  use c, hc
  rw [← toNNReal_lt_toNNReal_iff hb]
  convert h
  rw [toNNReal_mul (by norm_cast; exact hc.le)]
  simp

section NormedSpace

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

variable {f : E → F} {x₀ x y : E} {n : ℕ}

variable [CompleteSpace F]

/-- *Taylor's theorem with remainder in integral form*. -/
theorem map_eq_sum_add_integral_iteratedFDeriv (hf : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
    ContDiffAt ℝ (n + 1) f (x₀ + t • (x - x₀))) :
    f x = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x₀ (fun _ ↦ x - x₀)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) f (x₀ + t • (x - x₀)) (fun _ ↦ x - x₀) := by
  convert map_add_eq_sum_add_integral_iteratedFDeriv hf
  module

end NormedSpace

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Topology

variable {f : E → E} {x₀ x y : E} {n : ℕ} {δ₀ : ℝ}

/-- If `-fderiv ℝ f x₀` is coercive, then there exists a neighborhood of `x₀` such that
`inner ℝ (x - x₀) (f x) < 0` for all `x ≠ x₀` in that neighborhood. -/
public theorem eventually_inner_neg (hf : f x₀ = 0)
    (h : IsCoercive ((innerSL ℝ) ∘L (-fderiv ℝ f x₀))) (hdiff : DifferentiableAt ℝ f x₀) :
    ∀ᶠ x in 𝓝 x₀, x ≠ x₀ → inner ℝ (x - x₀) (f x) < 0 := by
  obtain ⟨C, hC, hcoer⟩ := h
  have hev := hdiff.hasFDerivAt.isLittleO.def (c := C / 2) (by positivity)
  filter_upwards [hev] with x hx hxx₀
  set u : E := x - x₀ with hu
  have hupos : 0 < ‖u‖ := by simpa [hu, sub_eq_zero] using hxx₀
  have hlin : inner ℝ u ((fderiv ℝ f x₀) u) ≤ -(C * ‖u‖ * ‖u‖) := by
    have key : C * ‖u‖ * ‖u‖ ≤ -inner ℝ ((fderiv ℝ f x₀) u) u := by
      simpa [innerSL_apply_apply ℝ] using hcoer u
    grind [real_inner_comm]
  have hrem : inner ℝ u (f x - f x₀ - (fderiv ℝ f x₀) u) ≤ C / 2 * ‖u‖ * ‖u‖ := by
    calc inner ℝ u (f x - f x₀ - (fderiv ℝ f x₀) u)
        ≤ ‖u‖ * ‖f x - f x₀ - (fderiv ℝ f x₀) u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (C / 2 * ‖u‖) := by gcongr
      _ = C / 2 * ‖u‖ * ‖u‖ := by ring
  have hsplit : inner ℝ u (f x) =
      inner ℝ u ((fderiv ℝ f x₀) u) + inner ℝ u (f x - f x₀ - (fderiv ℝ f x₀) u) := by
    rw [← inner_add_right]
    congr 1
    grind
  have hpos : 0 < C / 2 * ‖u‖ * ‖u‖ := by positivity
  grind

/-- If `-fderiv ℝ f x₀` is coercive, then there exists a neighborhood of `x₀` such that
`inner ℝ (x - x₀) (f x) < 0` for all `x ≠ x₀` in that neighborhood. -/
public theorem exists_inner_neg (hf : f x₀ = 0) (h : IsCoercive ((innerSL ℝ) ∘L (-fderiv ℝ f x₀)))
    (hdiff : DifferentiableAt ℝ f x₀) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ Metric.ball x₀ δ, x ≠ x₀ → inner ℝ (x - x₀) (f x) < 0 :=
  Metric.eventually_nhds_iff.mp (eventually_inner_neg hf h hdiff)

end InnerProductSpace

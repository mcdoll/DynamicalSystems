/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.Example

import Mathlib.Analysis.InnerProductSpace.Calculus
import DynamicalSystems.Mathlib.Analysis.Calculus.IsStrictLocalMax
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear

/-! # Stability of fixed points by linearization

This file proves that a fixed point `x₀` of an autonomous ODE is stable if the `-fderiv ℝ f x₀` is
coercive, in the sense that `innerSL ℝ ∘L (-fderiv ℝ f x₀)` is a coercive bilinear form.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {f : E → E} {Φ : AutonomousFlow ℝ E} {x₀ : E}

open scoped Topology

theorem exists_isLyapunovOnIn (hf : DifferentiableAt ℝ f x₀) (hx₀ : f x₀ = 0)
    (h : IsCoercive (innerSL ℝ ∘L (-fderiv ℝ f x₀)))
    (hΦ : ∀ x₀, IsIntegralCurve (Φ · x₀) (fun _ ↦ f)) :
    ∃ δ, 0 < δ ∧ IsLyapunovOnIn (fun x ↦ ‖x - x₀‖ ^ 2) Φ { p | ‖p - x₀‖ ^ 2 ≤ δ} (Set.Ici 0) := by
  obtain ⟨δ, hδ, h⟩ := exists_inner_neg hx₀ h hf
  use (δ / 2) ^ 2, by positivity
  have hs : IsOpen { x | ‖x - x₀‖ < δ } := isOpen_lt (by fun_prop) (by fun_prop)
  apply AutonomousFlow.isLyapunovOnIn_of_fderiv (fun _ ↦ by positivity) hs ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [sq_le_sq₀ (by positivity) (by positivity)] at hx
    grw [hx]
    simpa
  · simp_rw [← real_inner_self_eq_norm_sq]
    fun_prop
  · intro x t
    apply (hΦ x t).differentiableAt
  · intro x hx
    suffices inner ℝ (x - x₀) (f x) ≤ 0 by
      simp_rw [← real_inner_self_eq_norm_sq]
      rw [fderiv_inner_apply ℝ (by fun_prop) (by fun_prop), real_inner_comm (x - x₀)]
      simpa [fderiv_sub_const x₀, (hΦ x 0).deriv]
    by_cases! h' : x ≠ x₀
    · apply (h _ _ h').le
      rwa [mem_ball_iff_norm]
    · simp [h']

variable [ProperSpace E]

/-- Let `f` be a vector field and `Φ` its fundamental solution.
A fixed point `x₀` of `Φ` is stable if `inner ℝ y (fderiv ℝ f x₀ y) ≤ -C ‖y‖ ^ 2` for some `C > 0`.

The condition on the derivative is phrased in terms of `IsCoercive`.
-/
theorem isStableOn_of_isCoercive_inner_comp_neg_fderiv (hf : DifferentiableAt ℝ f x₀)
    (hx₀ : f x₀ = 0) (hΦ : ∀ x₀, IsIntegralCurve (Φ · x₀) (fun _ ↦ f))
    (h : IsCoercive (innerSL ℝ ∘L (-fderiv ℝ f x₀))) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  obtain ⟨δ₀, hδ₀, h_lya⟩ := exists_isLyapunovOnIn hf hx₀ h hΦ
  apply h_lya.isStableOn_nhds (δ₀ := δ₀) ?_ ?_ ?_ hδ₀
  · simp
  · convert isCompact_closedBall x₀ (δ₀ ^ ((1 : ℝ) / 2))
    ext x
    simp only [Set.mem_ofPred_eq, one_div, Metric.mem_closedBall]
    rw [Real.le_rpow_inv_iff_of_pos (by positivity) hδ₀.le (by norm_num), dist_eq_norm]
    simp
  · simp [sub_eq_zero]
  · simp

open scoped NNReal

/-- For a globally Lipschitz continuous `f` with `f x₀ = 0` and
`inner ℝ y (fderiv ℝ f x₀ y) ≤ -C ‖y‖ ^ 2` for some `C > 0` there exists a fundamental solution that
is stable at `x₀`.

The corresponding uniqueness result is `LipschitzWith.unique_autonomousFlow`. -/
example {K : ℝ≥0} (hf : LipschitzWith K f) (hfx₀ : DifferentiableAt ℝ f x₀)
    (hx₀ : f x₀ = 0) (h : IsCoercive (innerSL ℝ ∘L (-fderiv ℝ f x₀))) :
    ∃ Φ : AutonomousFlow ℝ E, (𝓝 x₀).IsStableOn Φ (Set.Ici 0) ∧
      ∀ x₀, IsIntegralCurve (Φ · x₀) (fun _ ↦ f) := by
  obtain ⟨Φ, hΦ⟩ := hf.exists_autonomousFlow
  use Φ
  refine ⟨?_, hΦ⟩
  exact isStableOn_of_isCoercive_inner_comp_neg_fderiv hfx₀ hx₀ hΦ h

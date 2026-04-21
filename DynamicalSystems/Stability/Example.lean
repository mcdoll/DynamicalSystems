/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.LaSalle
public import DynamicalSystems.Stability.Lyapunov

@[expose] public noncomputable section

variable {r : ℝ}

/-! # Stability of the system `d/dt x = r x`

In this file we prove that the system `d/dt x = r x` is asymptotically stable using
Lyapunov's theorem and LaSalle's invariance principle.

The Lyapunov function is `x ↦ x ^ 2` and it is decreasing if `r ≤ 0` and it is strictly
decreasing if `r < 0`. Hence, if `r < 0` the fixed point `x = 0` is asymptotically stable.

While it is easy to deduce this from the explicit solution operator `Φ t x = x * e ^ (r * t)`, we
will prove the theorem using Lyapunov's theorem and LaSalle's theorem as a test that these results
are usable. -/

variable (r) in
theorem isLinearlyBddVectorField_smul : IsLinearlyBddVectorField (fun x : ℝ ↦ r • x) where
  differentiable := by fun_prop
  exists_bound := by
    use |r|
    intro x
    rw [fderiv_fun_const_smul (by fun_prop)]
    simp only [fderiv_id', norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le

variable (r) in
/-- The flow of the vector field `x ↦ r • x`. -/
def smulFlow : Flow ℝ ℝ :=
  (isLinearlyBddVectorField_smul r).flow

@[simp]
theorem deriv_smulFlow {x : ℝ} : deriv (smulFlow r · x) 0 = r • (smulFlow r 0 x) :=
  (isLinearlyBddVectorField_smul r).deriv_flow _ _

/-- The function `x ↦ x ^ 2` is a Lyapunov function for the system `d/dt x = (-r) • x`. -/
theorem isLyapunov_sq_smulFlow (hr : 0 ≤ r) : IsLyapunov (fun x : ℝ ↦ x ^ 2) (smulFlow (-r)) := by
  apply Flow.isLyapunov (by fun_prop) (fun x ↦ by positivity) (by fun_prop)
  intro x
  simp
  ring_nf
  positivity

open scoped Topology
open Filter

/-- The origin is stable under the forward flow of `d/dt x = r x` -/
theorem isStableOn_smulFlow (hr : 0 ≤ r) : (𝓝 0).IsStableOn (smulFlow (-r)) (Set.Ici 0) := by
  apply (isLyapunov_sq_smulFlow hr).isStableOn_nhds (by simp) (by simp) zero_lt_one
  simp only [sq_le_one_iff_abs_le_one]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact Metric.isBounded_of_abs_le 1

/-- The origin is asymptotic stable under the forward flow of `d/dt x = r x` -/
theorem tendsto_smulFlow (hr : 0 < r) (x : ℝ) : Tendsto (smulFlow (-r) · x) atTop (𝓝 0) := by
  apply (isLyapunov_sq_smulFlow hr.le).tendsto_of_fderiv_nonpos (isCompact_closedBall 0 ‖x‖)
  · intro y hy
    simp [sq_le_sq.mp hy]
  · fun_prop
  · fun_prop
  · intro y hy h
    simp
    ring_nf
    positivity

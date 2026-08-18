/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.LaSalle
public import DynamicalSystems.Stability.Lyapunov
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Stability of the system `d/dt x = r x`

In this file we prove that the system `d/dt x = r x` is asymptotically stable using
Lyapunov's theorem and LaSalle's invariance principle.

The Lyapunov function is `x ↦ x ^ 2` and it is decreasing if `r ≤ 0` and it is strictly
decreasing if `r < 0`. Hence, if `r < 0` the fixed point `x = 0` is asymptotically stable.

While it is easy to deduce this from the explicit solution operator `Φ t x = x * e ^ (r * t)`, we
will prove the theorem using Lyapunov's theorem and LaSalle's theorem as a test that these results
are usable. -/

@[expose] public noncomputable section

variable {𝕜 E 𝔸 : Type*} {r : ℝ}

section ExponentialFlow

variable [RCLike 𝕜] [NormedAddCommGroup E] [CompleteSpace E]

section NormedSpace

variable [NormedSpace 𝕜 E]

def ContinuousLinearMap.expFlow (A : E →L[𝕜] E) : Flow 𝕜 E where
  toFun t x := NormedSpace.exp (t • A) x
  cont' := by
    have : NormedAlgebra ℚ (E →L[𝕜] E) := by
      apply NormedAlgebra.restrictScalars (𝕜' := 𝕜)
    fun_prop
  map_add' t t' := by
    intro x
    rw [add_smul]
    have : NormedAlgebra ℚ (E →L[𝕜] E) := by
      apply NormedAlgebra.restrictScalars (𝕜' := 𝕜)
    rw [NormedSpace.exp_add_of_commute, ContinuousLinearMap.mul_def]
    · simp
    · exact (Commute.smul_right rfl t').smul_left t
  map_zero' := by
    intro x
    simp

variable {A : E →L[𝕜] E}

@[simp]
theorem expFlow_apply (t : 𝕜) (x : E) : A.expFlow t x = NormedSpace.exp (t • A) x := rfl

@[fun_prop]
theorem differentiable_expFlow (x : E) : Differentiable 𝕜 (A.expFlow · x) := by
  fun_prop

theorem deriv_expFlow (x : E) : deriv (A.expFlow · x) 0 = A x := by
  simp only [expFlow_apply]
  rw [deriv_clm_apply (by fun_prop) (by fun_prop)]
  simp only [zero_smul, NormedSpace.exp_zero, deriv_const', one_apply_eq_self, add_zero]
  congr
  refine HasDerivAt.deriv ?_
  convert! hasDerivAt_exp_smul_const A (0 : 𝕜)
  simp

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

variable {A : E →L[ℝ] E}

attribute [fun_prop] differentiable_inner

/-- The function `x ↦ ⟪A x, x⟫` is a Lyapunov function for the system `d/dt x = (-A) • x`. -/
theorem isLyapunov_sq_expFlow (hA : A.IsPositive) :
    IsLyapunov (fun x : E ↦ inner ℝ (A x) x) ((-A).expFlow) := by
  apply Flow.isLyapunov (by fun_prop) hA.inner_nonneg_left (by fun_prop)
  intro x
  rw [deriv_expFlow, fderiv_inner_apply ℝ (by fun_prop) (by fun_prop)]
  suffices -‖A x‖ ^ 2 ≤ inner ℝ (A (A x)) x by simpa
  simp [hA.inner_left_eq_inner_right]

end InnerProductSpace

end ExponentialFlow

/-variable (r) in
theorem isLinearlyBddVectorField_smul : IsLinearlyBddVectorField (fun x : ℝ ↦ r • x) where
  differentiable := by fun_prop
  exists_bound := by
    use |r|
    intro x
    rw [fderiv_fun_const_smul (by fun_prop)]
    simp only [fderiv_fun_id, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le-/

variable (r) in
/-- The flow of the vector field `x ↦ r • x`. -/
def smulFlow : Flow ℝ ℝ := (r • ContinuousLinearMap.id ℝ ℝ).expFlow
  --(isLinearlyBddVectorField_smul r).flow

@[simp]
theorem deriv_smulFlow {x : ℝ} : deriv (smulFlow r · x) 0 = r * x := by
  rw [smulFlow, deriv_expFlow]
  simp

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

/-- The origin is globally asymptotic stable under the forward flow of `d/dt x = r x` -/
theorem tendsto_smulFlow (hr : 0 < r) (x : ℝ) : Tendsto (smulFlow (-r) · x) atTop (𝓝 0) := by
  apply (isLyapunov_sq_smulFlow hr.le).tendsto_of_fderiv_neg (isCompact_closedBall 0 ‖x‖)
  · intro y hy
    simp [sq_le_sq.mp hy]
  · fun_prop
  · fun_prop
  · intro y hy h
    simp
    ring_nf
    positivity

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.LaSalle
public import DynamicalSystems.Lyapunov

@[expose] public noncomputable section

variable {r : ℝ}

/- We want to prove that `d/dt x = r x` is asymptotically stable at `x₀ = 0` for `r < 0`, without
calculating the flow explicitly, `Φ(t, x) = x e ^ (r t)`. -/

-- 1) We probably need to claim that there exists a solution operator
-- 2) The Lyapunov function is given by `V(x) = x ^ 2`
-- 3) The Lie derivative is `2 r x ^ 2`, so decreasing for `r < 0`.
-- 4) Now apply LaSalle and Lyapunov


theorem isCompleteVectorField_smul_id : IsCompleteVectorField (fun x : ℝ ↦ r • x) := by sorry

theorem lipschitzWith_smul_id : LipschitzWith ‖r‖₊ (fun x : ℝ ↦ r • x) := by sorry

variable (r) in
def smul_id_flow : Flow ℝ ℝ :=
  isCompleteVectorField_smul_id.flow (K := ‖r‖₊) lipschitzWith_smul_id

/-- The function `x ↦ x ^ 2` is a Lyapunov function for the system `d/dt x = r x`. -/
theorem foo (hr : r ≤ 0) : IsLyapunov (fun x : ℝ ↦ x ^ 2) (smul_id_flow r) :=
  Flow.isLyapunov isCompleteVectorField_smul_id lipschitzWith_smul_id (fun x ↦ ?_) ?_ (fun x ↦ ?_)
where finally
  · positivity
  · fun_prop
  · simp only [smul_eq_mul, fderiv_eq_smul_deriv, differentiableAt_fun_id, deriv_fun_pow,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one]
    ring_nf
    rw [mul_assoc]
    apply mul_nonpos_of_nonpos_of_nonneg hr
    positivity

open scoped Topology
open Filter

/-- An easy example of using Lyapunov's theorem. -/
theorem stable (hr : r ≤ 0) : (𝓝 0).IsStableOn (smul_id_flow r) (Set.Ici 0) := by
  apply (foo hr).isStableOn (by simp) (by simp) zero_lt_one
  simp only [sq_le_one_iff_abs_le_one]
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact Metric.isBounded_of_abs_le 1

/-- An easy example of using LaSalle's principle. -/
theorem asymptotic_stable (x : ℝ) : Tendsto (smul_id_flow r · x) atTop (𝓝 0) := by
  sorry

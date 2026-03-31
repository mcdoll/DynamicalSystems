/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Transform
public import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall2
public import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique

@[expose] public noncomputable section

variable {E E' F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fundamental solution -/
structure IsFundamentalSolution (Φ : ℝ → E → E) (f : ℝ → E → E) : Prop where
  isIntegralCurve : ∀ x, IsIntegralCurve (Φ · x) f
  zero : Φ 0 = id

namespace IsFundamentalSolution

variable {Φ : ℝ → E → E} {f : ℝ → E → E}

theorem zero_apply (hΦ : IsFundamentalSolution Φ f) (x : E) : Φ 0 x = x := by
  rw [hΦ.zero, id_eq]

theorem differentiable (hΦ : IsFundamentalSolution Φ f) (x : E) : Differentiable ℝ (Φ · x) := by
  intro t
  apply (hΦ.isIntegralCurve x t).differentiableAt

protected
theorem deriv (hΦ : IsFundamentalSolution Φ f) {t : ℝ} (x : E) : deriv (Φ · x) t = f t (Φ t x) :=
  (hΦ.isIntegralCurve x t).deriv

open scoped NNReal

variable {K : ℝ≥0}

/-- The fundamental solution is continuous in the initial datum.

Todo: generalize to non-autonomous. -/
theorem continuous {v : E → E} (hΦ : IsFundamentalSolution Φ (fun _ ↦ v))
    (hv : LipschitzWith K v) :
    Continuous Φ.uncurry := by
  rw [Metric.continuous_iff]
  intro ⟨t₀, x₀⟩ ε hε
  have h_cont_x₀ : ContinuousAt (Φ · x₀) t₀ :=
    (hΦ.isIntegralCurve x₀).continuous.continuousAt
  rw [Metric.continuousAt_iff] at h_cont_x₀
  obtain ⟨δ₀, hδ₀, h_cont_x₀⟩ := h_cont_x₀ (ε / 2) (by positivity)
  use min δ₀ ((ε / 2) * Real.exp (- K * (|t₀| + δ₀) - 1/2)), by positivity
  intro ⟨t, x⟩ hy
  rw [Prod.dist_eq, max_lt_iff] at hy
  simp only [neg_mul, one_div] at hy
  obtain ⟨ht, hx⟩ := hy
  calc
    _ = dist (Φ t x) (Φ t₀ x₀) := by simp
    _ ≤ dist (Φ t x) (Φ t x₀) + dist (Φ t x₀) (Φ t₀ x₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := by
      gcongr
      · have hcont : ∀ x, ContinuousOn (Φ · x) (Set.uIcc 0 t) :=
          fun x ↦ (hΦ.isIntegralCurve x).continuous.continuousOn
        have h : ∀ x, ∀ t' ∈ Set.uIcc 0 t, HasDerivAt (Φ · x) (v (Φ t' x)) t' := by
          intro x t' ht'
          apply hΦ.isIntegralCurve
        have hdist : dist (Φ 0 x) (Φ 0 x₀) ≤ (ε / 2) * Real.exp (- K * |t| - 2⁻¹) := by
          rw [hΦ.zero_apply, hΦ.zero_apply]
          grw [hx, Std.min_le_right]
          gcongr
          simp only [neg_mul, neg_le_neg_iff]
          gcongr
          calc
            _ = |t₀ + (t - t₀)| := by congr; ring
            _ ≤ |t₀| + |t - t₀| := by apply abs_add_le
            _ ≤ |t₀| + δ₀ := by
              gcongr
              rw [← Real.norm_eq_abs, ← dist_eq_norm]
              grw [ht, Std.min_le_left]
        have := dist_le_of_trajectories_ODE' (fun _ _ ↦ hv) (hcont x) (h x) (hcont x₀) (h x₀) hdist
          t (by simp)
        simp only [neg_mul, sub_zero] at this
        grw [this]
        rw [mul_assoc, ← lt_div_iff₀' (by positivity), div_self (by positivity), ← Real.exp_add,
          Real.exp_lt_one_iff]
        grind
      · apply h_cont_x₀
        apply lt_of_lt_of_le ht Std.min_le_left
    _ = _ := by ring

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem add_apply {v : E → E} (hΦ : IsFundamentalSolution Φ (fun _ ↦ v))
    (hv : LipschitzWith K v) (t t' : ℝ) (x : E) :
    Φ t (Φ t' x) = Φ (t + t') x := by
  set f := fun t ↦ Φ t (Φ t' x)
  set g := fun t ↦ Φ (t + t') x
  have hf : IsIntegralCurve f (fun _ ↦ v) := hΦ.isIntegralCurve (Φ t' x)
  have hg : IsIntegralCurve g (fun _ ↦ v) := (hΦ.isIntegralCurve x).comp_add t'
  have ht₀ : f 0 = g 0 := by
    unfold f g
    simp [hΦ.zero]
  apply congrFun <| hf.eq (fun _ ↦ hv.lipschitzOnWith) (fun _ ↦ Set.mem_univ _) hg
    (fun _ ↦ Set.mem_univ _) ht₀


end IsFundamentalSolution

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Transform
public import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall
public import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique
public import DynamicalSystems.Mathlib.Analysis.Calculus

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


end IsFundamentalSolution

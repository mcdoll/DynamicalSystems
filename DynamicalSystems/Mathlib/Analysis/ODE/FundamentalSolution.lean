/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence

/-! # Fundamental solutions

A fundamental solution is an autonomous flow `Φ` such that for each `x`, `Φ · x` is an integral
curve of the vector field `f`.

We show the elementary facts that fundamental solutions are differentiable in `t`-direction and
the derivative at `0` is the vector field evaluated at `x`.
-/

@[expose] public noncomputable section

namespace AutonomousFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Φ : AutonomousFlow ℝ E} {f : E → E}

variable (Φ f) in
/-- A fundamental solution for an autonomous system given by `d/dt x = f(x)` . -/
def IsFundamentalSolution : Prop :=
  ∀ x, IsIntegralCurve (Φ · x) (fun _ ↦ f)

variable {f : E → E}

namespace IsFundamentalSolution

protected
theorem deriv (h : Φ.IsFundamentalSolution f) (x : E) :
    deriv (Φ · x) 0 = f x := by
  refine HasDerivAt.deriv ?_
  simpa using h x 0

@[fun_prop]
protected
theorem differentiableAt (h : Φ.IsFundamentalSolution f) (x : E) (t : ℝ) :
    DifferentiableAt ℝ (Φ · x) t :=
  (h x t).differentiableAt

@[fun_prop]
protected
theorem differentiable (h : Φ.IsFundamentalSolution f) (x : E) :
    Differentiable ℝ (Φ · x) :=
  (h.differentiableAt x ·)

end IsFundamentalSolution

end AutonomousFlow

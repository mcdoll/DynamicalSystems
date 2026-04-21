/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.Lyapunov
public import DynamicalSystems.ComparisonFunctions

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f g : E ≃L[ℝ] E} (n : ℤ)

example : f * g = g.trans f := by
  exact ContinuousLinearEquiv.ext rfl

example (x : E) : f ⁻¹ x = f.symm x := by
  apply?

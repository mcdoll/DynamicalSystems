/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Dynamics.Basic

/-! # Abstract formulation of solution operators for non-autonomous ODEs

In this file we define an abstract version of the solution operator for a non-autonomous ODE.

-/

public section

variable {τ E F : Type*}

variable (τ E) in
/-- A non-autonomous flow is a map `u` from `τ × τ × E` to `E` such that `u t₀ t₀ x = x` and
`u t₀ t₁ (u t₁ t₂ x) = u t₀ t₂ x`.

We do not impose any continuity property. -/
structure NonautonomousFlow where
  /-- The underlying map -/
  toFun : τ → τ → E → E
  /-- Consistency: the solution operator acts as the identity at initial time -/
  map_id (t₀ : τ) (x : E) : toFun t₀ t₀ x = x
  /-- Semigroup property: the solution operator satisfies `Φ t₀ t₁ (Φ t₁ t₂ x) = Φ t₀ t₂ x` -/
  map_comp (t₀ t₁ t₂ : τ) (x : E) : toFun t₀ t₁ (toFun t₁ t₂ x) = toFun t₀ t₂ x

namespace NonautonomousFlow

end NonautonomousFlow

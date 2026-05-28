/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Dynamics.Basic

/-! # Abstract formulation of solution operators for non-autonomous ODEs

In this file we define

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
  map_id (t₀ : τ) (x : E) : toFun t₀ t₀ x = x
  map_comp (t₀ t₁ t₂ : τ) (x : E) : toFun t₀ t₁ (toFun t₁ t₂ x) = toFun t₀ t₂ x

namespace NonautonomousFlow

end NonautonomousFlow

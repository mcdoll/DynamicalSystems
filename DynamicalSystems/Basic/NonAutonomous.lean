/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Algebra.Group.End

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
  toFun : τ → E → τ → E
  /-- Consistency: the solution operator acts as the identity at initial time -/
  map_id (t₀ : τ) (x : E) : toFun t₀ x t₀ = x
  /-- Semigroup property: the solution operator satisfies `Φ t₀ t₁ (Φ t₁ t₂ x) = Φ t₀ t₂ x` -/
  map_comp (t₀ t₁ t₂ : τ) (x : E) : toFun t₀ (toFun t₁ x t₂) t₁ = toFun t₀ x t₂

attribute [coe] NonautonomousFlow.toFun

attribute [simp] NonautonomousFlow.map_id

variable (τ E) in
/-- An autonomous flow is a map `u` from `τ × E` to `E` such that `u 0 x = x` and
`u t₀ (u t₁ x) = u (t₀ + t₁) x`.

As opposed to mathlib's `Flow`, we do not impose any continuity property. -/
structure AutonomousFlow [AddZero τ] where
  /-- The underlying map -/
  toFun : τ → E → E
  /-- Initial conditions -/
  map_id (x : E) : toFun 0 x = x
  /-- Semigroup property -/
  map_comp (t t' : τ) (x : E) : toFun t (toFun t' x) = toFun (t + t') x

attribute [coe] AutonomousFlow.toFun

attribute [simp] AutonomousFlow.map_id

namespace NonautonomousFlow

instance : CoeFun (NonautonomousFlow τ E) (fun _ ↦ τ → E → τ → E) where
  coe L := L.toFun

variable {Φ : NonautonomousFlow τ E}

/-- A non-autonomous flow that satisfies `Φ (t₀ + s) x (t + s) = Φ t₀ x t` defines an autonomous
flow. -/
@[expose] def toAutonomousFlow [AddCommMonoid τ] (Φ : NonautonomousFlow τ E)
    (h : ∀ s t₀ t x, Φ (t₀ + s) x (t + s) = Φ t₀ x t) : AutonomousFlow τ E where
  toFun t x := Φ 0 x t
  map_id x := by simp
  map_comp t t' x := by
    have : Φ 0 x t' = Φ t x (t + t') := by
      simp [← h t 0 t' x, add_comm]
    rw [this, map_comp]

@[simp]
theorem toFun_toAutonomousFlow [AddCommMonoid τ] (h : ∀ s t₀ t x, Φ (t₀ + s) x (t + s) = Φ t₀ x t) :
  (Φ.toAutonomousFlow h).toFun = fun t x ↦ Φ 0 x t := rfl

end NonautonomousFlow

namespace AutonomousFlow

section AddZero

variable [AddZero τ]

instance : CoeFun (AutonomousFlow τ E) (fun _ ↦ τ → E → E) where
  coe L := L.toFun

@[ext]
theorem ext {Φ₁ Φ₂ : AutonomousFlow τ E} (h : ∀ t x, Φ₁ t x = Φ₂ t x) : Φ₁ = Φ₂ := by
  cases Φ₁; cases Φ₂
  simp only [mk.injEq]
  ext
  apply h

/-- Any function defines a autonomous `ℕ`-flow. -/
def _root_.Function.autonomousFlow (f : E → E) : AutonomousFlow ℕ E where
  toFun t := f^[t]
  map_id x := by simp
  map_comp t t' x := by rw [Function.iterate_add_apply]

/-- Any equivalence defines a autonomous `ℤ`-flow. -/
def _root_.Equiv.autonomousFlow (f : E ≃ E) : AutonomousFlow ℤ E where
  toFun t := ↑(f ^ t)
  map_id x := by simp
  map_comp t t' x := by simp [zpow_add f t t']

end AddZero

section AddCommGroup

variable [AddCommGroup τ]

variable {Φ : AutonomousFlow τ E}

variable (Φ) in
/-- Every autonomous flow defines a non-autonomous flow -/
def toNonautonomousFlow : NonautonomousFlow τ E where
  toFun t₀ x t := Φ (t - t₀) x
  map_id t₀ x := by simp
  map_comp t₀ t₁ t₂ x := by rw [map_comp]; congr; grind

@[simp]
theorem toNonautonomousFlow_apply (t₀ t : τ) (x : E) :
    Φ.toNonautonomousFlow t₀ x t = Φ (t - t₀) x := by
  rfl

end AddCommGroup

end AutonomousFlow

namespace Flow

variable [TopologicalSpace τ] [TopologicalSpace E] [AddZero τ]

variable {Φ : Flow τ E}

variable (Φ) in
/-- Every continuous flow defines a autonomous flow -/
@[expose] def toAutonomousFlow : AutonomousFlow τ E where
  toFun := Φ
  map_id := Φ.map_zero'
  map_comp t t' x := (map_add Φ t t' x).symm

@[simp]
theorem toAutonomousFlow_apply (t : τ) : Φ.toAutonomousFlow t = Φ t := rfl

@[simp]
theorem coe_toAutonomousFlow_apply : Φ.toAutonomousFlow.toFun = Φ.toFun := rfl

end Flow

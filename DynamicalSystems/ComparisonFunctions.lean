/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Basic

@[expose] public noncomputable section

open NNReal Filter Topology

/-- A function of class `K`. -/
@[fun_prop]
structure MemK (f : ℝ≥0 → ℝ≥0) : Prop where
  cont : Continuous f
  strictMono : StrictMono f
  zero : f 0 = 0

/-- A function of class `K_∞`. -/
@[fun_prop]
structure MemKI (f : ℝ≥0 → ℝ≥0) : Prop extends MemK f where
  tendsto : Tendsto f atTop atTop

/-- A function of class `KL`. -/
@[fun_prop]
structure MemKL (f : ℝ → ℝ≥0 → ℝ≥0) : Prop where
  cont : Continuous f.uncurry
  strictMono : ∀ x, StrictMono (f x)
  zero : ∀ x, f x 0 = 0
  antitone : ∀ y, Antitone (f · y)
  tendsto : ∀ y, Tendsto (f · y) atTop (𝓝 0)

variable {f : ℝ → ℝ≥0 → ℝ≥0}

theorem MemKL.memK (hf : MemKL f) (x : ℝ) : MemK (f x) := by
  refine ⟨?_, hf.strictMono x, hf.zero x⟩
  have : Continuous f.uncurry := hf.cont
  fun_prop

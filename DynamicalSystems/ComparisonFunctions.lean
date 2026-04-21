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

namespace MemK

variable {f g : ℝ≥0 → ℝ≥0}

theorem injective (hf : MemK f) : Function.Injective f :=
  hf.strictMono.injective

@[fun_prop]
theorem comp (hf : MemK f) (hg : MemK g) : MemK (f ∘ g) where
  cont := hf.cont.comp hg.cont
  strictMono := hf.strictMono.comp hg.strictMono
  zero := by simp [hf.zero, hg.zero]

@[fun_prop]
theorem invFun (hf : MemK f) (hf' : f.Bijective) : MemK f.invFun where
  cont := by
    rw [Metric.continuous_iff]
    intro y₀ ε hε
    set x₀ := f.invFun y₀
    --set y₁ := f (x₀ - ε)
    --set y₂ := f (x₀ + ε)
    -- take δ := min (y₀ - y₁) (y₂ - y₀)
    --apply?
    sorry
  strictMono := by
    rw [StrictMono]
    by_contra!
    obtain ⟨y₁, y₂, hy, h⟩ := this
    set x₁ := f.invFun y₁
    set x₂ := f.invFun y₂
    have hx : x₂ ≤ x₁ := by
      sorry
    have := hf.strictMono.monotone hx
    sorry
  zero := by
    convert Function.leftInverse_invFun hf.injective 0
    simp [hf.zero]

end MemK


#check f⁻¹

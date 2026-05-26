/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

public section

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

structure IsCaratheodoryOn (f : ℝ → E → E) (s : Set ℝ × Set E) where
  cont : ∀ᵐ t ∂volume.restrict s.1, Continuous (f t)
  meas : ∀ x ∈ s.2, Measurable (f · x)



structure IsCaratheodory (f : ℝ → E → E) where
  cont : ∀ᵐ t, Continuous (f t)
  meas : ∀ x, Measurable (f · x)

variable {f : ℝ → E → E} {m : ℝ → ℝ} {γ : ℝ → E}

theorem IsCaratheodory.comp_aemeasurable (h : IsCaratheodory f) (hm : Integrable m)
    (hγ : AEMeasurable γ) : AEMeasurable (fun t ↦ f t (γ t)) := by
  -- measurability of the composition: this is highly nontrivial and hinges on the fact that
  -- `f` is a Caratheodory function, see Lemma 2.4 in Rindler
  sorry


theorem IsCaratheodory.comp_integrable [BorelSpace E] [SecondCountableTopology E]
    (h : IsCaratheodory f) (hm : Integrable m) (hfm : ∀ t x, ‖f t x‖ ≤ m t)
    (hγ : AEMeasurable γ) : Integrable (fun t ↦ f t (γ t)) := by
  constructor
  · exact (h.comp_aemeasurable hm hγ).aestronglyMeasurable
  calc
    _ ≤ ∫⁻ t, ‖m t‖ₑ := by
      gcongr with t
      rw [enorm_le_iff_norm_le]
      grw [hfm]
      exact Real.le_norm_self (m t)
    _ < _ := hm.hasFiniteIntegral

/-- `IsAEIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for almost all
`t ∈ s`. -/
def IsAEIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ᵐ t ∂volume.restrict s, HasDerivWithinAt γ (v t (γ t)) s t

/-- `IsAEIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v` almost everywhere.
That is, `γ t` is tangent to `v t (γ t)` for almost all `t : ℝ`. -/
def IsAEIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ᵐ t : ℝ, HasDerivAt γ (v t (γ t)) t

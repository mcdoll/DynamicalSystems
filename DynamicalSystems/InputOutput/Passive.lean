/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
public import DynamicalSystems.InputOutput.Causal

/-! # Passive maps

-/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α 𝕜 E F G : Type*}

section definition

variable [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace E] [TopologicalSpace F]
  [ENorm E] [ENorm F]

/-- A map `f` is passive with bound `β` if for all admissible functions we have the bound
`- ∫ x in s t, B (u x) (f u x) ∂μ ≤ β`.

The most common choices for `B` are
- `inner ℝ`: passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2`: input strictly passive
- `fun x y ↦ inner ℝ x y - ε • ‖y‖ ^ 2`: output strictly passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2 - ε • ‖y‖ ^ 2`: very strictly passive -/
def SetRel.IsPassiveWith (f : SetRel (α → E) (α → F)) (B : E → F → ℝ) (s : ι → Set α) (β : ℝ)
    (p q : ℝ≥0∞) [p.HolderConjugate q] (μ : Measure α := by volume_tac) : Prop :=
  ∀ ⦃t u y⦄, MemLpLoc u p μ ∧ MemLpLoc y q μ ∧ (u, y) ∈ f → - ∫ x in s t, B (u x) (y x) ∂μ ≤ β

/-- A map `f` is passive with bound `β` if for all admissible functions we have the bound
`- ∫ x in s t, B (u x) (f u x) ∂μ ≤ β`.

The most common choices for `B` are
- `inner ℝ`: passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2`: input strictly passive
- `fun x y ↦ inner ℝ x y - ε • ‖y‖ ^ 2`: output strictly passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2 - ε • ‖y‖ ^ 2`: very strictly passive -/
structure Function.IsPassiveWith (f : (α → E) → α → F) (B : E → F → ℝ) (s : ι → Set α) (β : ℝ)
    (p q : ℝ≥0∞) [p.HolderConjugate q] (μ : Measure α := by volume_tac) : Prop where
  memLpLoc : ∀ ⦃u⦄, MemLpLoc u p μ → MemLpLoc (f u) q μ
  integral_le :
    ∀ ⦃t u⦄, MemLpLoc u p μ → - ∫ x in s t, B (u x) (f u x) ∂μ ≤ β

namespace Function.IsPassiveWith

variable {f : (α → E) → α → F} {B B₁ B₂ : E → F → ℝ} {s : ι → Set α} {β β' : ℝ} {p q : ℝ≥0∞}
    [p.HolderConjugate q] {μ : Measure α}

theorem add_right
    (hs : ∀ t, IsCompact (s t))
    (hB₁ : f.IsPassiveWith B₁ s β p q μ)
    (hB₂ : f.IsPassiveWith B₂ s β' p q μ)
    (hB₁' : ∀ (ν : Measure α) (u : α → E) (v : α → F), MemLp u p ν ∧ MemLp v q ν → Integrable (fun x ↦ B₁ (u x) (v x)) ν) :
    f.IsPassiveWith (B₁ + B₂) s (β + β') p q μ := by
  constructor
  · intro u hu
    apply hB₁.memLpLoc hu
  · intro t u hu
    calc
      _ = -∫ (x : α) in s t, B₁ (u x) (f u x) ∂μ + (-∫ (x : α) in s t, B₂ (u x) (f u x) ∂μ) := by
        simp only [Pi.add_apply]
        rw [integral_add ?_ ?_]
        · ring
        · apply hB₁' (μ.restrict (s t)) u (f u) ⟨?_, ?_⟩
          · sorry
          · sorry
        · sorry
      _ ≤ _ := by
        gcongr
        · apply hB₁.integral_le hu
        · apply hB₂.integral_le hu


theorem graph_isPassiveWith (h : f.IsPassiveWith B s β p q μ) :
    f.graph.IsPassiveWith B s β p q μ := by
  intro t u y ⟨hu, hy, hf⟩
  simp only [mem_graph] at hf
  rw [← hf]
  exact h.integral_le hu

end Function.IsPassiveWith

end definition

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

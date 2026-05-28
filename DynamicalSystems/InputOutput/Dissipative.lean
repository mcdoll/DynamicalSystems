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

/-! # Dissipative maps

-/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α 𝕜 E F G : Type*}

variable [MeasurableSpace α] [Bornology α]

variable (B : E → F → ℝ) {s : ι → Set α}

/-- A map `f` is dissipative with bound `β` if for all admissible functions we have the bound
`∫ x in s t, B (u x) (f u x) ∂μ ≤ - β`.

The most common choices for `B` are
- `inner ℝ`: passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2`: input strictly passive
- `fun x y ↦ inner ℝ x y - ε • ‖y‖ ^ 2`: output strictly passive
- `fun x y ↦ inner ℝ x y - δ • ‖x‖ ^ 2 - ε • ‖y‖ ^ 2`: very strictly passive -/
def IsDissipativeWith (f : (α → E) → α → F) (β : ℝ) (P : (α → E) → Prop)
    (μ : Measure α := by volume_tac) : Prop :=
  ∀ ⦃t⦄, MeasurableSet (s t) → ∀ ⦃u⦄, P u → ∫ x in s t, B (u x) (f u x) ∂μ ≤ - β

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

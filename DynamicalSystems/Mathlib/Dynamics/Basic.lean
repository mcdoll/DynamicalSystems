/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Analysis.ODE.Transform

public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz
public import DynamicalSystems.Mathlib.Analysis.Calculus.Flow

/-! # Basics of dynamical systems -/

@[expose] public noncomputable section

section Abstract

/-- A flow on a topological space `α` by an additive topological
monoid `τ` is a continuous monoid action of `τ` on `α`. -/
structure FlowOn (τ : Type*) [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ] (α : Type*)
  [TopologicalSpace α] (sₜ : AddSubmonoid τ) (sₓ : Set α) where
  /-- The map `τ → α → α` underlying a flow of `τ` on `α`. -/
  toFun : τ → α → α
  cont' : ContinuousOn (Function.uncurry toFun) (sₜ ×ˢ sₓ)
  map_add' : ∀ ⦃t₁ t₂ : τ⦄ (_ht₁ : t₁ ∈ sₜ) (_ht₂ : t₂ ∈ sₜ) ⦃x⦄ (_hx : x ∈ sₓ),
    toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
  map_zero' : ∀ x, toFun 0 x = x




end Abstract

section Continuous

/-! ### Flows of vector fields -/

-- A vector field is complete if for every `x₀` the integral curve exists for all time


variable {E : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]


end Continuous

section Differentiable

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {Φ Φ' : Flow ℝ E} {x : E} {t : ℝ}

theorem Flow.isCompleteVectorField (hΦ : ∀ x, Differentiable ℝ (Φ · x)) :
    IsCompleteVectorField (fun _ x ↦ deriv (Φ · x) 0) := by
  intro t₀ x
  use fun t ↦ Φ (t - t₀) x
  simp only [sub_self, map_zero, id_eq, true_and]
  rw [← isIntegralCurve_comp_add (dt := t₀)]
  have : IsIntegralCurve (Φ · x) (fun _ x ↦ deriv (Φ · x) 0) := by
    intro t
    simp only [← map_add]
    convert (hΦ x t).hasDerivAt using 1
    convert deriv_comp_add_const (Φ · x) t 0
    simp
  convert! this
  simp

proof_wanted flow_congr (hΦ : ∀ x, Differentiable ℝ (Φ · x)) (hΦ' : ∀ x, Differentiable ℝ (Φ' · x))
    (h : ∀ x, deriv (Φ · x) 0 = deriv (Φ' · x) 0) : Φ = Φ'

/-- A vector field `f : E → E` is called linearly bounded if it is differentiable and its derivative
is uniformly bounded. -/
structure IsLinearlyBddVectorField (f : E → E) : Prop where
  differentiable : Differentiable ℝ f
  exists_bound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C

namespace IsLinearlyBddVectorField

open NNReal

variable {f : E → E}

open Classical in
/-- A bound for a linearly bounded vector field.

Note that this bound is not unique. -/
protected
def bound (hf : IsLinearlyBddVectorField f) : ℝ := hf.exists_bound.choose

theorem norm_fderiv_le_bound (hf : IsLinearlyBddVectorField f) (x : E) :
    ‖fderiv ℝ f x‖ ≤ hf.bound := hf.exists_bound.choose_spec x

theorem bound_nonneg (hf : IsLinearlyBddVectorField f) :
    0 ≤ hf.bound := by
  grw [← hf.norm_fderiv_le_bound 0, ← norm_nonneg]

/-- A bound for a linearly bounded vector field.

Note that this bound is not unique. -/
def nnbound (hf : IsLinearlyBddVectorField f) : ℝ≥0 :=
  ⟨hf.bound, hf.bound_nonneg⟩

@[simp, norm_cast]
theorem coe_nnbound (hf : IsLinearlyBddVectorField f) :
    (hf.nnbound : ℝ) = hf.bound := rfl

theorem nnnorm_fderiv_le_nnbound (hf : IsLinearlyBddVectorField f) (x : E) :
    ‖fderiv ℝ f x‖₊ ≤ hf.nnbound := by
  simp [← NNReal.coe_le_coe, hf.norm_fderiv_le_bound]

theorem lipschitzWith (hf : IsLinearlyBddVectorField f) :
    LipschitzWith hf.nnbound f :=
  lipschitzWith_of_nnnorm_fderiv_le hf.differentiable hf.nnnorm_fderiv_le_nnbound

proof_wanted isCompleteVectorField (hf : IsLinearlyBddVectorField f) :
    IsCompleteVectorField (fun _ ↦ f)
  -- this follows from Theorem 2.17 of Teschl and the fundamental theorem of calculus

/- the following statements need the definition `IsCompleteVectorField.flow`

/-- The flow of a linearly bounded vector field. -/
def flow (hf : IsLinearlyBddVectorField f) : Flow ℝ E :=
  hf.isCompleteVectorField.flow hf.lipschitzWith.locallyLipschitz

@[simp]
theorem deriv_flow (hf : IsLinearlyBddVectorField f) (t : ℝ) (x : E) :
    deriv (hf.flow · x) t = f (hf.flow t x) :=
  hf.isCompleteVectorField.deriv_flow hf.lipschitzWith.locallyLipschitz t x

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_comp_flow (hf : IsLinearlyBddVectorField f) {v : E → F} (hv : Differentiable ℝ v)
    (t : ℝ) (x : E) :
    deriv (v <| hf.flow · x) t = fderiv ℝ v (hf.flow t x) (f <| hf.flow t x) :=
  hf.isCompleteVectorField.deriv_comp_flow hv hf.lipschitzWith.locallyLipschitz t x

-/

end IsLinearlyBddVectorField

end Differentiable

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.OmegaLimit
public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution
--public import Mathlib.Topology.Order.MonotoneConvergence


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


section Discrete

variable {α : Type*}

variable {f : α ≃ α} {n m : ℤ} {x : α}

variable (f) in
theorem Equiv.zpow_add_apply : (f ^ (n + m)) x = (f ^ n) ((f ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, zpow_add]

variable (f) in
protected theorem Equiv.zpow_mul {n m : ℤ} : f ^ (n * m) = (f ^ n) ^ m := by
  rw [zpow_mul]

namespace Homeomorph

variable [TopologicalSpace α] {f : Homeomorph α α}

instance : Pow (Homeomorph α α) ℕ where
  pow f n := {
    toEquiv := f ^ n
    continuous_toFun := f.continuous_toFun.iterate _
    continuous_invFun := f.continuous_invFun.iterate _ }

variable {n : ℕ}

@[simp]
theorem npow_zero : f ^ 0 = Homeomorph.refl α := rfl

@[simp]
theorem npow_one : f ^ 1 = f := rfl

instance : Pow (Homeomorph α α) ℤ where
  pow f n := {
    toEquiv := f ^ n
    continuous_toFun := by
      cases n with
      | ofNat n => apply f.continuous_toFun.iterate
      | negSucc n => apply f.continuous_invFun.iterate
    continuous_invFun := by
      cases n with
      | ofNat n => apply f.continuous_invFun.iterate
      | negSucc n => apply f.continuous_toFun.iterate }

variable {n : ℤ}

variable {f g : Homeomorph α α}

@[simp]
theorem zpow_zero : f ^ (0 : ℤ) = Homeomorph.refl α := rfl

@[simp]
theorem zpow_one : f ^ (1 : ℤ) = f := rfl

@[simp]
theorem zpow_neg_one : f ^ (-1) = f.symm := rfl

theorem zpow_mul {n m : ℤ} : f ^ (n * m) = (f ^ n) ^ m := by
  ext x
  apply Equiv.ext_iff.mp
  apply _root_.zpow_mul

theorem zpow_neg : f ^ (-n) = f.symm ^ n := by
  rw [neg_eq_neg_one_mul, f.zpow_mul, f.zpow_neg_one]

@[simp, norm_cast]
theorem zpow_coe {n : ℕ} : f ^ (n : ℤ) = f ^ n := rfl

theorem zpow_add_apply {n m : ℤ} : (f ^ (n + m)) x = (f ^ n) ((f ^ m) x) :=
  f.toEquiv.zpow_add_apply

end Homeomorph

variable [TopologicalSpace α] (f : Homeomorph α α)

/-- The discrete flow `ℤ → α → α` induced by a homeomorphism `f : α → α`. -/
def Homeomorph.toFlow (f : Homeomorph α α) : Flow ℤ α where
  toFun n x := (f ^ n) x
  cont' := by
    rw [continuous_prod_of_discrete_left]
    intro n
    simp only [Function.uncurry_apply_pair]
    fun_prop
  map_add' n₁ n₂ := by
    intro x
    exact f.zpow_add_apply
  map_zero' x := by simp


end Discrete

section Continuous

/-! ### Flows of vector fields -/

-- A vector field is complete if for every `x₀` the integral curve exists for all time


variable {E : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vector field is complete if for every point there exists a global integral curve
`γ : ℝ → E`. -/
def IsCompleteVectorField (f : E → E) : Prop :=
  ∀ x, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ ↦ f)

variable {x : E}
variable {f : E → E}

namespace IsCompleteVectorField

/-- The flow of a vector field at a point `x`. -/
def flowAt (hf : IsCompleteVectorField f) (x : E) : ℝ → E :=
  (hf x).choose

@[simp]
theorem flowAt_zero (hf : IsCompleteVectorField f) (x : E) : hf.flowAt x 0 = x :=
  (hf x).choose_spec.left

theorem flowAt_isIntegralCurve (hf : IsCompleteVectorField f) (x : E) :
    IsIntegralCurve (hf.flowAt x) (fun _ ↦ f) :=
  (hf x).choose_spec.right

theorem flowAt_isFundamentalSolution (hf : IsCompleteVectorField f) :
    IsFundamentalSolution (fun t x ↦ hf.flowAt x t) (fun _ ↦ f) where
  isIntegralCurve x := hf.flowAt_isIntegralCurve x
  zero := by
    ext x
    exact hf.flowAt_zero x

@[fun_prop]
theorem differentiable_flowAt (hf : IsCompleteVectorField f) {x : E} :
    Differentiable ℝ (hf.flowAt x) :=
  (hf.flowAt_isIntegralCurve x · |>.differentiableAt)

open scoped NNReal

variable {K : ℝ≥0}

/-- Every complete and Lipschitz vector field admits a global flow. -/
def flow (hf : IsCompleteVectorField f) (h : LipschitzWith K f) : Flow ℝ E where
  toFun t x := hf.flowAt x t
  cont' := hf.flowAt_isFundamentalSolution.continuous h
  map_add' := (hf.flowAt_isFundamentalSolution.add_apply h · · · |>.symm)
  map_zero' := by simp

/-@[fun_prop]
theorem differentiable_flow (hf : IsCompleteVectorField f) (h : LipschitzWith K f) (x : E) :
    Differentiable ℝ (hf.flow h · x) := by fun_prop-/

@[simp]
theorem deriv_flow (hf : IsCompleteVectorField f) (h : LipschitzWith K f) (t : ℝ) (x : E) :
    deriv (hf.flow h · x) t = f (hf.flow h t x) :=
  (hf.flowAt_isIntegralCurve x t).deriv

example (hf : IsCompleteVectorField f) (h : LipschitzWith K f) (x : E) :
    deriv (hf.flow h · x) 0 = f x := by
  simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_comp_flow {v : E → F} (hv : Differentiable ℝ v) (hf : IsCompleteVectorField f)
    (h : LipschitzWith K f) (t : ℝ) (x : E) :
    deriv (v <| hf.flow h · x) t = fderiv ℝ v (hf.flow h t x) (f <| hf.flow h t x) := calc
  _ = (fderiv ℝ v (hf.flow h t x)) (deriv (hf.flow h · x) t) := by
    apply fderiv_comp_deriv t (by fun_prop) (by fun_prop)
  _ = _ := by rw [hf.deriv_flow]

end IsCompleteVectorField

end Continuous

section Differentiable

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {Φ Φ' : Flow ℝ E} {x : E} {t : ℝ}

theorem DifferentiableAt.deriv_eq_deriv_zero (h : ∀ x, DifferentiableAt ℝ (Φ · x) 0) :
    deriv (Φ · x) t = deriv (Φ · (Φ t x)) 0 := calc
  _ = deriv (fun s ↦ (Φ (s - t) (Φ t x))) t := by
    congr
    ext s
    rw [← Φ.map_add']
    grind
  _ = deriv (fun s : ℝ ↦ s - t) t • deriv (Φ · (Φ t x)) ((fun s : ℝ ↦ s - t) t) :=
    deriv.scomp (h := (· - t)) (g₁ := (Φ · (Φ t x))) t (by simp [h (Φ t x)]) (by fun_prop)
  _ = _ := by
    simp

theorem deriv_comp_flow {v : E → F} (hv : Differentiable ℝ v) (h : ∀ x, Differentiable ℝ (Φ · x))
    (t : ℝ) (x : E) :
    deriv (v <| Φ · x) t = fderiv ℝ v (Φ t x) (deriv (Φ · (Φ t x)) 0) := calc
  _ = (fderiv ℝ v (Φ t x)) (deriv (Φ · x) t) := by
    apply fderiv_comp_deriv t (by fun_prop) (by fun_prop)
  _ = _ := by
    rw [DifferentiableAt.deriv_eq_deriv_zero (by fun_prop)]

theorem Flow.isCompleteVectorField (hΦ : ∀ x, Differentiable ℝ (Φ · x)) :
    IsCompleteVectorField (fun x ↦ deriv (Φ · x) 0) := by
  intro x
  use (Φ · x)
  simp only [Flow.map_zero, id_eq, true_and]
  intro t
  convert ((hΦ x).differentiableAt (x := t)).hasDerivAt using 1
  calc
    deriv (Φ · (Φ t x)) 0 = deriv (fun s ↦ Φ (s + t) x) 0 := by
      congr
      ext y
      exact (Flow.map_add Φ y t x).symm
    _ = (deriv (· + t) 0) • deriv (Φ · x) ((· + t) 0) :=
      deriv.scomp 0 (hΦ x).differentiableAt (by fun_prop)
    _ = _ := by simp

theorem flow_congr (hΦ : ∀ x, Differentiable ℝ (Φ · x)) (hΦ' : ∀ x, Differentiable ℝ (Φ' · x))
    (h : ∀ x, deriv (Φ · x) 0 = deriv (Φ' · x) 0) : Φ = Φ' := by
  ext t x
  sorry

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

theorem isCompleteVectorField (hf : IsLinearlyBddVectorField f) :
    IsCompleteVectorField f := by
  intro x
  -- this follows from Theorem 2.17 of Teschl and the fundamental theorem of calculus
  sorry

/-- The flow of a linearly bounded vector field. -/
def flow (hf : IsLinearlyBddVectorField f) : Flow ℝ E :=
  hf.isCompleteVectorField.flow hf.lipschitzWith

@[simp]
theorem deriv_flow (hf : IsLinearlyBddVectorField f) (t : ℝ) (x : E) :
    deriv (hf.flow · x) t = f (hf.flow t x) :=
  hf.isCompleteVectorField.deriv_flow hf.lipschitzWith t x

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_comp_flow (hf : IsLinearlyBddVectorField f) {v : E → F} (hv : Differentiable ℝ v)
    (t : ℝ) (x : E) :
    deriv (v <| hf.flow · x) t = fderiv ℝ v (hf.flow t x) (f <| hf.flow t x) :=
  hf.isCompleteVectorField.deriv_comp_flow hv hf.lipschitzWith t x


end IsLinearlyBddVectorField

end Differentiable

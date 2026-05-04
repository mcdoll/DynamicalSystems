/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz
public import DynamicalSystems.Mathlib.Analysis.ODE.Transform

@[expose] public noncomputable section

variable {E E' F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

section NonAutonomous

/-- A fundamental solution for non-autonomous systems. -/
structure IsFundamentalSolution (Φ : ℝ → E → ℝ → E) (f : ℝ → E → E) : Prop where
  isIntegralCurve : ∀ t₀ x, IsIntegralCurve (Φ t₀ x) f
  initial : ∀ t₀ x₀, Φ t₀ x₀ t₀ = x₀

namespace IsFundamentalSolution

variable {Φ Φ' : ℝ → E → ℝ → E} {f : ℝ → E → E}

protected
theorem deriv (hΦ : IsFundamentalSolution Φ f) {t₀ t : ℝ} {x₀ : E} :
    deriv (Φ t₀ x₀) t = f t (Φ t₀ x₀ t) :=
  (hΦ.isIntegralCurve t₀ x₀ t).deriv

protected
theorem differentiableAt (hΦ : IsFundamentalSolution Φ f) (t₀ t : ℝ) (x₀ : E) :
    DifferentiableAt ℝ (Φ t₀ x₀) t :=
  (hΦ.isIntegralCurve t₀ x₀ t).differentiableAt

theorem continuous (hΦ : IsFundamentalSolution Φ f)
    (hf : UniformlyLocallyLipschitz f) (hf' : Continuous f) (t₀ : ℝ) :
    Continuous (Φ t₀).uncurry := by
  sorry

theorem unique (hΦ : IsFundamentalSolution Φ f) (hΦ' : IsFundamentalSolution Φ f)
    (hf : UniformlyLocallyLipschitz f) (hf' : Continuous f) :
    Φ = Φ' := by
  sorry

section Linear

variable (L : ℝ → E →L[ℝ] E) (X : ℝ → ℝ → E →L[ℝ] E)

theorem linear_fundamental_solution (hX₀ : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id _ _)
    (hX : ∀ t₀ t, deriv (X t₀ ·) t = L t ∘L X t₀ t) :
    IsFundamentalSolution (fun t₀ x t ↦ X t₀ t x) (L · ·) := by
  sorry

/-- The operator solving the inhomogeneous ODE `d/dx x = L(t) x + g t` given a solution operator
`X : ℝ → ℝ → E →L[ℝ] E`. -/
def duhamelOperator (X : ℝ → ℝ → E →L[ℝ] E) (g : ℝ → E) (t₀ : ℝ) (x₀ : E) (t : ℝ) : E :=
  X t₀ t x₀ + ∫ τ in t₀..t, X τ t (g τ)

variable {g : ℝ → E}

theorem duhamelOperator_initial (hX₀ : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id _ _)
    (t₀ : ℝ) (x₀ : E) : duhamelOperator X g t₀ x₀ t₀ = x₀ := by
  simp [duhamelOperator, hX₀ t₀]

theorem duhamelOperator_isIntegralCurve
    (hX : ∀ t₀ t, deriv (X t₀ ·) t = L t ∘L X t₀ t) (t₀ : ℝ) (x₀ : E) (t : ℝ) :
    deriv (duhamelOperator X g t₀ x₀) t = L t (duhamelOperator X g t₀ x₀ t) + g t := by
  sorry

end Linear

end IsFundamentalSolution

/-- A vector field is complete if for every point there exists a global integral curve
`γ : ℝ → E`. -/
def IsCompleteVectorField (f : ℝ → E → E) : Prop :=
  ∀ t₀ x₀, ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurve γ f

namespace IsCompleteVectorField

variable {f : ℝ → E → E}

/-- The flow of a vector field at a point `x`. -/
def flowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) : ℝ → E :=
  (hf t₀ x₀).choose

@[simp]
theorem flowAt_zero (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    hf.flowAt t₀ x₀ t₀ = x₀ :=
  (hf t₀ x₀).choose_spec.left

theorem flowAt_isIntegralCurve (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    IsIntegralCurve (hf.flowAt t₀ x₀) f :=
  (hf t₀ x₀).choose_spec.right

theorem flowAt_isFundamentalSolution (hf : IsCompleteVectorField f) :
    IsFundamentalSolution hf.flowAt f where
  isIntegralCurve := hf.flowAt_isIntegralCurve
  initial := hf.flowAt_zero

@[fun_prop]
theorem differentiable_flowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    Differentiable ℝ (hf.flowAt t₀ x₀) :=
  (hf.flowAt_isIntegralCurve t₀ x₀ · |>.differentiableAt)

/-- The flow of a vector field as a continuous map `ℝ → E`. -/
def contFlowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) : C(ℝ, E) where
  toFun := hf.flowAt t₀ x₀
  continuous_toFun := (hf.differentiable_flowAt _ _).continuous

@[simp]
theorem contFlowAt_apply (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) (t : ℝ) :
  hf.contFlowAt t₀ x₀ t = hf.flowAt t₀ x₀ t := rfl

end IsCompleteVectorField

variable {f : ℝ → E → E}

theorem UniformlyLocallyLipschitz.isCompleteVectorField (hf : UniformlyLocallyLipschitz f)
    (hf' : Continuous f)
    (hf'' : ∀ t, ∃ a b, ∀ x, ‖f t x‖ ≤ a + b * ‖x‖) :
    IsCompleteVectorField f := by
  intro t₀ x₀
  sorry

end NonAutonomous

section Autonomous

variable (f : E → E) (Φ : E → ℝ → E)

theorem isFundamentalSolution_iff' :
    IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f) ↔
    ∀ x, IsIntegralCurve (Φ x) (fun _ ↦ f) ∧ Φ x 0 = x := by
  constructor
  · intro h x
    exact ⟨by simpa using h.isIntegralCurve 0 x, by simpa using h.initial 0 x⟩
  · intro h
    exact ⟨fun t₀ x₀ ↦ by simpa using (h x₀).1.comp_sub t₀, fun t₀ x₀ ↦ by simpa using (h x₀).2⟩

variable {K : NNReal}

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply'
    (hΦ : IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f))
    (hv : LipschitzWith K f) (t t' : ℝ) (x : E) :
    Φ (Φ x t') t = Φ x (t + t') := by
  set γ₁ := Φ (Φ x t')
  set γ₂ := fun t ↦ Φ x (t + t')
  rw [isFundamentalSolution_iff'] at hΦ
  have := (hΦ x).1.comp_add t'
  have hf : IsIntegralCurve γ₁ (fun _ ↦ f) := (hΦ (Φ x t')).1
  have hg : IsIntegralCurve γ₂ (fun _ ↦ f) := (hΦ x).1.comp_add t'
  have ht₀ : γ₁ 0 = γ₂ 0 := by
    unfold γ₁ γ₂
    simp [(hΦ (Φ x t')).2]
  apply congrFun <| hf.eq (fun _ ↦ hv.lipschitzOnWith) (fun _ ↦ Set.mem_univ _) hg
    (fun _ ↦ Set.mem_univ _) ht₀

variable {Φ' : ℝ → E → ℝ → E}

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply''
    (hΦ : IsFundamentalSolution Φ' (fun _ ↦ f))
    (hv : LocallyLipschitz f) (t₀ t t' : ℝ) (x : E) :
    Φ' t₀ (Φ' t₀ x t') t = Φ' t₀ x (t + t') := by
  sorry

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply
    (hΦ : IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f))
    (hv : LocallyLipschitz f) (t t' : ℝ) (x : E) :
    Φ (Φ x t') t = Φ x (t + t') := by
  sorry

end Autonomous

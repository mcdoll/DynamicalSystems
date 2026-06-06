/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence

/-! # Causal operators and finite gain

-/


@[expose] public noncomputable section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

attribute [local instance] Measure.Subtype.measureSpace

variable {ι α 𝕜 𝕜' E E₁ E₂ F F₁ F₂ : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E]


section funlike_instance

variable [FunLike F ι α]

instance Function.instFunLike : FunLike (ι → α) ι α where
  coe := id
  coe_injective' _ _ := by simp

/-- The map between `ℝ≥0` and the subtype. -/
def NNReal.toSubtype (x : ℝ≥0) : {x : ℝ // x ≥ 0} := x

instance instMeasureSpaceNNReal : MeasureSpace ℝ≥0 where
  volume := (volume : Measure {x : ℝ // x ≥ 0}).comap NNReal.toSubtype

end funlike_instance

section InputToState

variable [NormedSpace ℝ E]

theorem globalExistence {f : E → E} {g : ℝ → E} (hf : LocallyLipschitz f) (hg : Continuous g)
    (hf' : ∃ a b, ∀ x, ‖f x‖ ≤ a + b * ‖x‖) : IsCompleteVectorField (fun t x ↦ f x + g t) := by
  apply UniformlyLocallyLipschitz.isCompleteVectorField
  · apply hf.uniformlyLocallyLipschitz.add (UniformlyLocallyLipschitz.const g)
  · fun_prop
  · intro t
    obtain ⟨a, b, h⟩ := hf'
    use a + ‖g t‖, b
    intro x
    grw [norm_add_le, h x]
    apply le_of_eq
    ring

variable (E E₁ E₂) in
/-- A state system is function `ℝ → E₁` to `ℝ → E₂` given implicitly by solving an ordinary
differential equation.

More precisely, let `u : ℝ → E₁` be the input, then we solve the ODE `d/dt x = f(x) + g(u(t))` with
initial condition `x(0) = x₀`. The output is then given by `y(t) = h(x(t))` for some continuous
function `h`. -/
structure StateSystem [TopologicalSpace E₁] [TopologicalSpace E₂] where
  /-- The unforced dynamics -/
  f : E → E
  /-- The input function -/
  input : C(E₁, E)
  /-- The output function -/
  output : C(E, E₂)
  f_lip : LocallyLipschitz f
  f_est : ∃ a b, ∀ x, ‖f x‖ ≤ a + b * ‖x‖
  /-- The base point -/
  x₀ : E

namespace StateSystem

variable [TopologicalSpace E₁] [TopologicalSpace E₂] (h : StateSystem E E₁ E₂)

/-- The associated vector field -/
def vectorfield (u : C(ℝ, E₁)) (t : ℝ) (x : E) : E := h.f x + h.input (u t)

theorem isCompleteVectorfield (u : C(ℝ, E₁)) : IsCompleteVectorField (h.vectorfield u) :=
  globalExistence h.f_lip (h.input.continuous.comp u.continuous) h.f_est

/-- The map from inputs to the state. -/
def stateMap (u : C(ℝ, E₁)) : C(ℝ, E) where
  toFun := (h.isCompleteVectorfield u).flowAt 0 h.x₀
  continuous_toFun :=
    ((h.isCompleteVectorfield u).differentiable_flowAt _ _).continuous

/-- The map from inputs to outputs. -/
def ioMap (u : C(ℝ, E₁)) : C(ℝ, E₂) := h.output.comp (h.stateMap u)

end StateSystem

end InputToState

section StateSystem

/-! ## State systems
In this section, we define state systems, that is given `f, g, h`, and `x₀`, we have the
input-output system u ↦ y, where

d/dt x = f(x) + g(u(t))
x(0) = x₀
y(t) = h(x(t))

There are some subtle considerations here: to obtain global well-posedness, we will have to assume
that `f` is Lipschitz and linearly bounded, `g` and `h` are continuous.
The input-output map takes a continuous `u` to a continuous `y`
is continuous (then it is also locally in `Lp` ) also `h` has to be continuous for
-/

end StateSystem



variable [NormedAddCommGroup F] [Bornology α]

variable (f : (α → E) → α → E)


section ClosedLoop

/-- a closed loop -/
structure closedLoop (f₁ : (α → E) → α → F) (f₂ : (α → F) → α → E) (p : ℝ≥0∞) (μ : Measure α) where
  /-- foo -/
  e₁ : (α → E) → (α → F) → α → E
  /-- foo -/
  e₂ : (α → E) → (α → F) → α → F
  memLpLoc : ∀ u₁ u₂, MemLpLoc u₁ p μ ∧ MemLpLoc u₂ p μ →
    MemLpLoc (e₁ u₁ u₂) p μ ∧ MemLpLoc (e₂ u₁ u₂) p μ
  loop : ∀ u₁ u₂, MemLpLoc u₁ p μ ∧ MemLpLoc u₂ p μ →
    e₁ u₁ u₂ = u₁ - f₂ (e₂ u₁ u₂) ∧ e₂ u₁ u₂ = u₂ + f₁ (e₁ u₁ u₂)
  -- wrong: does not have uniqueness built in

variable {β₁ β₂ k₁ k₂} {f₁ : (α → E) → α → F} {f₂ : (α → F) → α → E} {s : ι → Set α} {p : ℝ≥0∞}
  {μ : Measure α}

/-- output of a closed loop -/
def closedLoop.out (l : closedLoop f₁ f₂ p μ) (u : α → E × F) (x : α) : F × E :=
  (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) x, f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) x)

@[simp]
theorem closedLoop.out_fst (l : closedLoop f₁ f₂ p μ) (u : α → E × F) (x : α) :
  (closedLoop.out l u x).1 = f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) x := rfl

@[simp]
theorem closedLoop.out_snd (l : closedLoop f₁ f₂ p μ) (u : α → E × F) (x : α) :
  (closedLoop.out l u x).2 = f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) x := rfl


/-- Pointwise product norm bound used before lifting closed-loop output
estimates to localized `eLpNorm` estimates. -/
theorem prod_norm_le_norm_fst_add_norm_snd (x : F × E) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  rw [Prod.norm_def]
  exact max_le
    (le_add_of_nonneg_right (norm_nonneg x.2))
    (le_add_of_nonneg_left (norm_nonneg x.1))


set_option linter.unusedSectionVars false in
/-- Product-valued `eLpNorm` split through the two coordinate embeddings.

This is the local measurable version needed before a closed-loop finite-gain
estimate can be assembled from the two component estimates. -/
theorem eLpNorm_prod_le_embedded_fst_add_embedded_snd
    {ν : Measure α}
    {v : α → F × E}
    (hv₁ : AEStronglyMeasurable ((fun x => ((v x).1, (0 : E))) : α → F × E) ν)
    (hv₂ : AEStronglyMeasurable ((fun x => ((0 : F), (v x).2)) : α → F × E) ν)
    (hp : 1 ≤ p) :
    eLpNorm v p ν ≤
      eLpNorm ((fun x => ((v x).1, (0 : E))) : α → F × E) p ν +
      eLpNorm ((fun x => ((0 : F), (v x).2)) : α → F × E) p ν := by
  have hdecomp :
      v =
        ((fun x => ((v x).1, (0 : E))) : α → F × E) +
        ((fun x => ((0 : F), (v x).2)) : α → F × E) := by
    funext x
    ext <;> simp
  calc
    eLpNorm v p ν =
        eLpNorm
          (((fun x => ((v x).1, (0 : E))) : α → F × E) +
            ((fun x => ((0 : F), (v x).2)) : α → F × E)) p ν := by
      exact congrArg (fun w => eLpNorm w p ν) hdecomp
    _ ≤
        eLpNorm ((fun x => ((v x).1, (0 : E))) : α → F × E) p ν +
          eLpNorm ((fun x => ((0 : F), (v x).2)) : α → F × E) p ν := by
      exact eLpNorm_add_le hv₁ hv₂ hp


set_option linter.unusedSectionVars false in
/-- First embedded coordinate has no larger `eLpNorm` than its scalar coordinate. -/
theorem eLpNorm_embedded_fst_le_coordinate
    {ν : Measure α}
    {v : α → F × E} :
    eLpNorm ((fun x => ((v x).1, (0 : E))) : α → F × E) p ν ≤
      eLpNorm (fun x => (v x).1) p ν := by
  exact eLpNorm_mono (fun x => by
    simp [Prod.norm_def, norm_nonneg])

set_option linter.unusedSectionVars false in
/-- Second embedded coordinate has no larger `eLpNorm` than its scalar coordinate. -/
theorem eLpNorm_embedded_snd_le_coordinate
    {ν : Measure α}
    {v : α → F × E} :
    eLpNorm ((fun x => ((0 : F), (v x).2)) : α → F × E) p ν ≤
      eLpNorm (fun x => (v x).2) p ν := by
  exact eLpNorm_mono (fun x => by
    simp [Prod.norm_def, norm_nonneg])


/-- First internal loop signal bound obtained from the structural loop equation
`e₁ = u₁ - f₂(e₂)` and `eLpNorm_sub_le`. -/
theorem closedLoop.internal_e₁_bound_from_loop
    (l : closedLoop f₁ f₂ p μ)
    (t : ι)
    (u : α → E × F)
    (hu : MemLpLoc u p μ)
    (hu₁_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.fst ∘ u) (μ.restrict (s t)))
    (hf₂_e₂_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ) :
    eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t)) ≤
      eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
        (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₂) := by
  have hu_components :
      MemLpLoc (Prod.fst ∘ u) p μ ∧
      MemLpLoc (Prod.snd ∘ u) p μ := by
    simpa [memLpLoc_prod_iff] using hu
  have hloop :=
    l.loop (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
  have hinternal_memLpLoc :=
    l.memLpLoc (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
  rcases hf₂ with ⟨_, hf₂_bound⟩
  have hf₂_component_bound :=
    hf₂_bound t (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) hinternal_memLpLoc.2
  have hsub :
      eLpNorm
        ((Prod.fst ∘ u) -
          f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        p (μ.restrict (s t)) ≤
        eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          eLpNorm
            (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
            p (μ.restrict (s t)) := by
    exact eLpNorm_sub_le hu₁_aestronglyMeasurable hf₂_e₂_aestronglyMeasurable hp
  calc
    eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t))
        =
        eLpNorm
          ((Prod.fst ∘ u) -
            f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
          p (μ.restrict (s t)) := by
          exact congrArg (fun w => eLpNorm w p (μ.restrict (s t))) hloop.1
    _ ≤
        eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          eLpNorm
            (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
            p (μ.restrict (s t)) :=
          hsub
    _ ≤
        eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂) := by
          exact add_le_add_right hf₂_component_bound _


/-- Second internal loop signal bound obtained from the structural loop equation
`e₂ = u₂ + f₁(e₁)` and `eLpNorm_add_le`. -/
theorem closedLoop.internal_e₂_bound_from_loop
    (l : closedLoop f₁ f₂ p μ)
    (t : ι)
    (u : α → E × F)
    (hu : MemLpLoc u p μ)
    (hu₂_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.snd ∘ u) (μ.restrict (s t)))
    (hf₁_e₁_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ) :
    eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t)) ≤
      eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
        (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₁) := by
  have hu_components :
      MemLpLoc (Prod.fst ∘ u) p μ ∧
      MemLpLoc (Prod.snd ∘ u) p μ := by
    simpa [memLpLoc_prod_iff] using hu
  have hloop :=
    l.loop (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
  have hinternal_memLpLoc :=
    l.memLpLoc (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
  rcases hf₁ with ⟨_, hf₁_bound⟩
  have hf₁_component_bound :=
    hf₁_bound t (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) hinternal_memLpLoc.1
  have hadd :
      eLpNorm
        ((Prod.snd ∘ u) +
          f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        p (μ.restrict (s t)) ≤
        eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          eLpNorm
            (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
            p (μ.restrict (s t)) := by
    exact eLpNorm_add_le hu₂_aestronglyMeasurable hf₁_e₁_aestronglyMeasurable hp
  calc
    eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t))
        =
        eLpNorm
          ((Prod.snd ∘ u) +
            f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
          p (μ.restrict (s t)) := by
          exact congrArg (fun w => eLpNorm w p (μ.restrict (s t))) hloop.2
    _ ≤
        eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          eLpNorm
            (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
            p (μ.restrict (s t)) :=
          hadd
    _ ≤
        eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁) := by
          exact add_le_add_right hf₁_component_bound _


/-- Coupled internal signal bound obtained by scaling and bundling the two
loop-equation coordinate bounds.

This is intentionally not the absorption step.  It prepares the ordered
`ENNReal` inequality system for the later small-gain contractive solver. -/
theorem closedLoop.coupled_internal_bounds
    (l : closedLoop f₁ f₂ p μ)
    (t : ι)
    (u : α → E × F)
    (hu : MemLpLoc u p μ)
    (hu₁_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.fst ∘ u) (μ.restrict (s t)))
    (hu₂_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.snd ∘ u) (μ.restrict (s t)))
    (hf₁_e₁_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hf₂_e₂_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ) :
    (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₁) +
    (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₂) ≤
    (k₁ *
      (eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
        (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₂)) + β₁) +
    (k₂ *
      (eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
        (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₁)) + β₂) := by
  have hb₁ :=
    l.internal_e₁_bound_from_loop
      t u hu hu₁_aestronglyMeasurable hf₂_e₂_aestronglyMeasurable hp hf₂
  have hb₂ :=
    l.internal_e₂_bound_from_loop
      t u hu hu₂_aestronglyMeasurable hf₁_e₁_aestronglyMeasurable hp hf₁
  have hscaled₁ :
      k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≤
      k₁ *
        (eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂)) := by
    exact mul_le_mul (le_refl (k₁ : ℝ≥0∞)) hb₁ (by exact zero_le) (by exact zero_le)
  have hscaled₂ :
      k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≤
      k₂ *
        (eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁)) := by
    exact mul_le_mul (le_refl (k₂ : ℝ≥0∞)) hb₂ (by exact zero_le) (by exact zero_le)
  have h₁ :
      k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) + β₁ ≤
      k₁ *
        (eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂)) + β₁ := by
    exact add_le_add hscaled₁ (le_refl (β₁ : ℝ≥0∞))
  have h₂ :
      k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) + β₂ ≤
      k₂ *
        (eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁)) + β₂ := by
    exact add_le_add hscaled₂ (le_refl (β₂ : ℝ≥0∞))
  exact add_le_add h₁ h₂


/-- Route from the coupled loop-equation bound to the exact internal-signal
bound required by `closedLoop.isFiniteGainStable`.

This theorem does not prove the contractive small-gain absorption.  It isolates
that remaining ordered-`ENNReal` algebra as the single hypothesis `hcontract`. -/
theorem closedLoop.internal_signal_to_external_eLpNorm_bound_from_contract_solver
    (l : closedLoop f₁ f₂ p μ)
    (t : ι)
    (u : α → E × F)
    (hu : MemLpLoc u p μ)
    (hu₁_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.fst ∘ u) (μ.restrict (s t)))
    (hu₂_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.snd ∘ u) (μ.restrict (s t)))
    (hf₁_e₁_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hf₂_e₂_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ)
    (hcontract :
      (k₁ *
        (eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂)) + β₁) +
      (k₂ *
        (eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁)) + β₂) ≤
      ((k₁ + k₂ + 2 * k₁ * k₂) / (1 - k₁ * k₂)) *
        eLpNorm u p (μ.restrict (s t)) +
        ((β₁ + k₁ * β₂ + β₂ + k₂ * β₁) / (1 - k₁ * k₂))) :
    (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₁) +
    (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₂) ≤
      ((k₁ + k₂ + 2 * k₁ * k₂) / (1 - k₁ * k₂)) *
        eLpNorm u p (μ.restrict (s t)) +
        ((β₁ + k₁ * β₂ + β₂ + k₂ * β₁) / (1 - k₁ * k₂)) := by
  exact le_trans
    (l.coupled_internal_bounds
      t u hu
      hu₁_aestronglyMeasurable
      hu₂_aestronglyMeasurable
      hf₁_e₁_aestronglyMeasurable
      hf₂_e₂_aestronglyMeasurable
      hp hf₁ hf₂)
    hcontract


/-- A closed loop whose selected internal signals depend causally on the external input.

This is intentionally separate from `closedLoop`: the base object remains an
existence witness, while this strengthened layer supplies the missing
well-posed/causal selector data needed for closed-loop causality. -/
structure wellPosedClosedLoop
    (f₁ : (α → E) → α → F)
    (f₂ : (α → F) → α → E)
    (s : ι → Set α)
    (p : ℝ≥0∞)
    (μ : Measure α) where
  toClosedLoop : closedLoop f₁ f₂ p μ
  e₁_isCausal :
    (fun u : α → E × F =>
      toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ
  e₂_isCausal :
    (fun u : α → E × F =>
      toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ


namespace wellPosedClosedLoop
/-- A well-posed closed loop of causal components has a causal output map. -/
theorem isCausal
    (l : wellPosedClosedLoop f₁ f₂ s p μ)
    (hs : ∀ t, MeasurableSet (s t))
    (hf₁ : f₁.IsCausal s p μ)
    (hf₂ : f₂.IsCausal s p μ) :
    (closedLoop.out l.toClosedLoop).IsCausal s p μ := by
  constructor
  · intro u hu
    rw [memLpLoc_prod_iff] at hu ⊢
    constructor
    · apply hf₁.memLpLoc
      exact (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ u)
        (Prod.snd ∘ u)
        hu).1
    · apply hf₂.memLpLoc
      exact (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ u)
        (Prod.snd ∘ u)
        hu).2
  · intro t u hu
    have hu_ind : MemLpLoc ((s t).indicator u) p μ :=
      hu.indicator (hs t)
    have hu_comp :
        MemLpLoc (Prod.fst ∘ u) p μ ∧
        MemLpLoc (Prod.snd ∘ u) p μ :=
      memLpLoc_prod_iff.mp hu
    have hu_ind_comp :
        MemLpLoc (Prod.fst ∘ ((s t).indicator u)) p μ ∧
        MemLpLoc (Prod.snd ∘ ((s t).indicator u)) p μ :=
      memLpLoc_prod_iff.mp hu_ind
    have he₁ :
        MemLpLoc
          (l.toClosedLoop.e₁
            (Prod.fst ∘ u)
            (Prod.snd ∘ u))
          p μ :=
      (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ u)
        (Prod.snd ∘ u)
        hu_comp).1
    have he₂ :
        MemLpLoc
          (l.toClosedLoop.e₂
            (Prod.fst ∘ u)
            (Prod.snd ∘ u))
          p μ :=
      (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ u)
        (Prod.snd ∘ u)
        hu_comp).2
    have he₁_ind :
        MemLpLoc
          (l.toClosedLoop.e₁
            (Prod.fst ∘ ((s t).indicator u))
            (Prod.snd ∘ ((s t).indicator u)))
          p μ :=
      (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ ((s t).indicator u))
        (Prod.snd ∘ ((s t).indicator u))
        hu_ind_comp).1
    have he₂_ind :
        MemLpLoc
          (l.toClosedLoop.e₂
            (Prod.fst ∘ ((s t).indicator u))
            (Prod.snd ∘ ((s t).indicator u)))
          p μ :=
      (l.toClosedLoop.memLpLoc
        (Prod.fst ∘ ((s t).indicator u))
        (Prod.snd ∘ ((s t).indicator u))
        hu_ind_comp).2
    have he₁_eq :
        (s t).indicator
            (l.toClosedLoop.e₁
              (Prod.fst ∘ ((s t).indicator u))
              (Prod.snd ∘ ((s t).indicator u)))
          =
        (s t).indicator
            (l.toClosedLoop.e₁
              (Prod.fst ∘ u)
              (Prod.snd ∘ u)) := by
      simpa using l.e₁_isCausal.causal t u hu
    have he₂_eq :
        (s t).indicator
            (l.toClosedLoop.e₂
              (Prod.fst ∘ ((s t).indicator u))
              (Prod.snd ∘ ((s t).indicator u)))
          =
        (s t).indicator
            (l.toClosedLoop.e₂
              (Prod.fst ∘ u)
              (Prod.snd ∘ u)) := by
      simpa using l.e₂_isCausal.causal t u hu
    have hf₁_eq :
        (s t).indicator
            (f₁
              (l.toClosedLoop.e₁
                (Prod.fst ∘ ((s t).indicator u))
                (Prod.snd ∘ ((s t).indicator u))))
          =
        (s t).indicator
            (f₁
              (l.toClosedLoop.e₁
                (Prod.fst ∘ u)
                (Prod.snd ∘ u))) :=
      hf₁.eq_of_eq he₁_ind he₁ he₁_eq
    have hf₂_eq :
        (s t).indicator
            (f₂
              (l.toClosedLoop.e₂
                (Prod.fst ∘ ((s t).indicator u))
                (Prod.snd ∘ ((s t).indicator u))))
          =
        (s t).indicator
            (f₂
              (l.toClosedLoop.e₂
                (Prod.fst ∘ u)
                (Prod.snd ∘ u))) :=
      hf₂.eq_of_eq he₂_ind he₂ he₂_eq
    ext x <;> by_cases hx : x ∈ s t
    · simpa [closedLoop.out, hx] using congrFun hf₁_eq x
    · simp [hx]
    · simpa [closedLoop.out, hx] using congrFun hf₂_eq x
    · simp [hx]
end wellPosedClosedLoop

/-- A well-posed closed loop carrying an explicit finite-gain certificate for
the closed-loop output map.

This is a certified layer above `wellPosedClosedLoop`: it does not derive the
small-gain theorem, uniqueness of internal signals, or component-gain closure. -/
structure certifiedFiniteGainClosedLoop
    (f₁ : (α → E) → α → F)
    (f₂ : (α → F) → α → E)
    (s : ι → Set α)
    (p : ℝ≥0∞)
    (μ : Measure α)
    (k bias : ℝ≥0) where
  toWellPosedClosedLoop : wellPosedClosedLoop f₁ f₂ s p μ
  out_isFiniteGainStableWith :
    (closedLoop.out toWellPosedClosedLoop.toClosedLoop).IsFiniteGainStableWith
      k bias s p μ

namespace certifiedFiniteGainClosedLoop

variable {k bias : ℝ≥0}

/-- The certified finite-gain layer still exposes closed-loop causality. -/
theorem isCausal
    (l : certifiedFiniteGainClosedLoop f₁ f₂ s p μ k bias)
    (hs : ∀ t, MeasurableSet (s t))
    (hf₁ : f₁.IsCausal s p μ)
    (hf₂ : f₂.IsCausal s p μ) :
    (closedLoop.out l.toWellPosedClosedLoop.toClosedLoop).IsCausal s p μ :=
  wellPosedClosedLoop.isCausal l.toWellPosedClosedLoop hs hf₁ hf₂

/-- The certified finite-gain layer exposes its supplied finite-gain certificate. -/
theorem isFiniteGainStableWith
    (l : certifiedFiniteGainClosedLoop f₁ f₂ s p μ k bias) :
    (closedLoop.out l.toWellPosedClosedLoop.toClosedLoop).IsFiniteGainStableWith
      k bias s p μ :=
  l.out_isFiniteGainStableWith

/-- Bundled causal and finite-gain facts for the certified closed-loop output. -/
theorem isCausal_and_isFiniteGainStableWith
    (l : certifiedFiniteGainClosedLoop f₁ f₂ s p μ k bias)
    (hs : ∀ t, MeasurableSet (s t))
    (hf₁ : f₁.IsCausal s p μ)
    (hf₂ : f₂.IsCausal s p μ) :
    (closedLoop.out l.toWellPosedClosedLoop.toClosedLoop).IsCausal s p μ ∧
      (closedLoop.out l.toWellPosedClosedLoop.toClosedLoop).IsFiniteGainStableWith
        k bias s p μ :=
  ⟨l.isCausal hs hf₁ hf₂, l.isFiniteGainStableWith⟩

end certifiedFiniteGainClosedLoop


theorem closedLoop.isCausal
    (l : closedLoop f₁ f₂ p μ)
    (hs : ∀ t, MeasurableSet (s t))
    (he₁ :
      (fun u : α → E × F =>
        l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (he₂ :
      (fun u : α → E × F =>
        l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (hf₁ : f₁.IsCausal s p μ)
    (hf₂ : f₂.IsCausal s p μ) :
    (closedLoop.out l).IsCausal s p μ := by
  exact wellPosedClosedLoop.isCausal
    ({ toClosedLoop := l
       e₁_isCausal := he₁
       e₂_isCausal := he₂ } :
      wellPosedClosedLoop f₁ f₂ s p μ)
    hs hf₁ hf₂

/-- foo -/
def closedLoopBias (k₁ k₂ β₁ β₂ : ℝ≥0) : ℝ≥0 :=
  (β₁ + k₁ * β₂ + β₂ + k₂ * β₁) / (1 - k₁ * k₂)

/-- foo -/
def closedLoopGain (k₁ k₂ _β₁ _β₂ : ℝ≥0) : ℝ≥0 :=
  (k₁ + k₂ + 2 * k₁ * k₂) / (1 - k₁ * k₂)

/-- The classical small-gain condition for two nonnegative gains. -/
def SmallGainCondition (k₁ k₂ : ℝ≥0) : Prop := k₁ * k₂ < 1


/-- Real positive-denominator division cancellation used by the small-gain
algebra solver. -/
theorem real_division_cancellation
    (S A B U d : ℝ)
    (hd_pos : 0 < d)
    (hmul : d * S ≤ A * U + B) :
    S ≤ (A / d) * U + B / d := by
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hdiv : S ≤ (A * U + B) / d := by
    rw [le_div_iff₀ hd_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrhs : (A * U + B) / d = (A / d) * U + B / d := by
    field_simp [hd_ne]
  simpa [hrhs] using hdiv

/-- Nonnegative real small-gain solver in division form. -/
theorem nnreal_small_gain_core_division
    (E₁ E₂ U k₁ k₂ β₁ β₂ : ℝ≥0)
    (h_small : k₁ * k₂ < 1)
    (hE₁ : E₁ ≤ U + (k₂ * E₂ + β₂))
    (hE₂ : E₂ ≤ U + (k₁ * E₁ + β₁)) :
    ((k₁ * E₁ + β₁) + (k₂ * E₂ + β₂)) ≤
      ((k₁ + k₂ + 2 * k₁ * k₂) / (1 - k₁ * k₂)) * U +
        ((β₁ + k₁ * β₂ + β₂ + k₂ * β₁) / (1 - k₁ * k₂)) := by
  have h₁ := mul_le_mul_of_nonneg_left hE₁ (show (0 : ℝ≥0) ≤ k₁ by exact zero_le)
  have h₂ := mul_le_mul_of_nonneg_left hE₂ (show (0 : ℝ≥0) ≤ k₂ by exact zero_le)
  rw [← NNReal.coe_le_coe]
  push_cast
  have hsmall_real : ((k₁ : ℝ) * (k₂ : ℝ)) < 1 := by
    exact_mod_cast h_small
  have hsub_real : ((1 - k₁ * k₂ : ℝ≥0) : ℝ) = 1 - (k₁ : ℝ) * (k₂ : ℝ) := by
    rw [NNReal.coe_sub]
    · simp
    · exact le_of_lt h_small
  rw [hsub_real]
  have h₁_real :
      (k₁ : ℝ) * E₁ ≤ k₁ * (U + (k₂ * E₂ + β₂)) := by
    exact_mod_cast h₁
  have h₂_real :
      (k₂ : ℝ) * E₂ ≤ k₂ * (U + (k₁ * E₁ + β₁)) := by
    exact_mod_cast h₂
  have hE₁_nonneg : (0 : ℝ) ≤ E₁ := E₁.2
  have hE₂_nonneg : (0 : ℝ) ≤ E₂ := E₂.2
  have hU_nonneg : (0 : ℝ) ≤ U := U.2
  have hk₁_nonneg : (0 : ℝ) ≤ k₁ := k₁.2
  have hk₂_nonneg : (0 : ℝ) ≤ k₂ := k₂.2
  have hβ₁_nonneg : (0 : ℝ) ≤ β₁ := β₁.2
  have hβ₂_nonneg : (0 : ℝ) ≤ β₂ := β₂.2
  have hden_pos : (0 : ℝ) < 1 - (k₁ : ℝ) * (k₂ : ℝ) := by
    nlinarith
  have hmul :
      (1 - (k₁ : ℝ) * (k₂ : ℝ)) *
          (((k₁ : ℝ) * E₁ + β₁) + ((k₂ : ℝ) * E₂ + β₂)) ≤
        ((k₁ : ℝ) + k₂ + 2 * k₁ * k₂) * U +
          (β₁ + k₁ * β₂ + β₂ + k₂ * β₁) := by
    nlinarith
  exact real_division_cancellation
    (((k₁ : ℝ) * E₁ + β₁) + ((k₂ : ℝ) * E₂ + β₂))
    ((k₁ : ℝ) + k₂ + 2 * k₁ * k₂)
    (β₁ + k₁ * β₂ + β₂ + k₂ * β₁)
    U
    (1 - (k₁ : ℝ) * (k₂ : ℝ))
    hden_pos
    hmul

/-- Finite right-hand side normalization for the first internal inequality. -/
theorem ennreal_finite_rhs₁_ne_top
    (E₂ U₁ : ℝ≥0∞)
    (k₂ β₂ : ℝ≥0)
    (hU₁_ne_top : U₁ ≠ ⊤)
    (hE₂_ne_top : E₂ ≠ ⊤) :
    U₁ + ((k₂ : ℝ≥0∞) * E₂ + β₂) ≠ ⊤ := by
  rw [← ENNReal.coe_toNNReal hU₁_ne_top,
      ← ENNReal.coe_toNNReal hE₂_ne_top,
      ← ENNReal.coe_mul,
      ← ENNReal.coe_add,
      ← ENNReal.coe_add]
  exact ENNReal.coe_ne_top

/-- `toNNReal` normalization for the first finite right-hand side. -/
theorem ennreal_finite_rhs₁_toNNReal
    (E₂ U₁ : ℝ≥0∞)
    (k₂ β₂ : ℝ≥0)
    (hU₁_ne_top : U₁ ≠ ⊤)
    (hE₂_ne_top : E₂ ≠ ⊤) :
    (U₁ + ((k₂ : ℝ≥0∞) * E₂ + β₂)).toNNReal =
      U₁.toNNReal + (k₂ * E₂.toNNReal + β₂) := by
  conv_lhs =>
    rw [← ENNReal.coe_toNNReal hU₁_ne_top,
        ← ENNReal.coe_toNNReal hE₂_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add,
        ENNReal.toNNReal_coe]

/-- Finite right-hand side normalization for the second internal inequality. -/
theorem ennreal_finite_rhs₂_ne_top
    (E₁ U₂ : ℝ≥0∞)
    (k₁ β₁ : ℝ≥0)
    (hU₂_ne_top : U₂ ≠ ⊤)
    (hE₁_ne_top : E₁ ≠ ⊤) :
    U₂ + ((k₁ : ℝ≥0∞) * E₁ + β₁) ≠ ⊤ := by
  rw [← ENNReal.coe_toNNReal hU₂_ne_top,
      ← ENNReal.coe_toNNReal hE₁_ne_top,
      ← ENNReal.coe_mul,
      ← ENNReal.coe_add,
      ← ENNReal.coe_add]
  exact ENNReal.coe_ne_top

/-- `toNNReal` normalization for the second finite right-hand side. -/
theorem ennreal_finite_rhs₂_toNNReal
    (E₁ U₂ : ℝ≥0∞)
    (k₁ β₁ : ℝ≥0)
    (hU₂_ne_top : U₂ ≠ ⊤)
    (hE₁_ne_top : E₁ ≠ ⊤) :
    (U₂ + ((k₁ : ℝ≥0∞) * E₁ + β₁)).toNNReal =
      U₂.toNNReal + (k₁ * E₁.toNNReal + β₁) := by
  conv_lhs =>
    rw [← ENNReal.coe_toNNReal hU₂_ne_top,
        ← ENNReal.coe_toNNReal hE₁_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add,
        ENNReal.toNNReal_coe]

/-- `toNNReal` normalization for the finite small-gain left-hand side. -/
theorem ennreal_final_lhs_toNNReal
    (E₁ E₂ : ℝ≥0∞)
    (k₁ k₂ β₁ β₂ : ℝ≥0)
    (hE₁_ne_top : E₁ ≠ ⊤)
    (hE₂_ne_top : E₂ ≠ ⊤) :
    (((k₁ : ℝ≥0∞) * E₁ + β₁) +
      ((k₂ : ℝ≥0∞) * E₂ + β₂)).toNNReal =
      (k₁ * E₁.toNNReal + β₁) +
        (k₂ * E₂.toNNReal + β₂) := by
  conv_lhs =>
    rw [← ENNReal.coe_toNNReal hE₁_ne_top,
        ← ENNReal.coe_toNNReal hE₂_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add,
        ENNReal.toNNReal_coe]

/-- `toNNReal` normalization for the finite small-gain right-hand side. -/
theorem ennreal_final_rhs_toNNReal
    (U : ℝ≥0∞)
    (k₁ k₂ β₁ β₂ : ℝ≥0)
    (hU_ne_top : U ≠ ⊤) :
    (closedLoopGain k₁ k₂ β₁ β₂ * U +
      closedLoopBias k₁ k₂ β₁ β₂).toNNReal =
      closedLoopGain k₁ k₂ β₁ β₂ * U.toNNReal +
        closedLoopBias k₁ k₂ β₁ β₂ := by
  conv_lhs =>
    rw [← ENNReal.coe_toNNReal hU_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add,
        ENNReal.toNNReal_coe]

/-- Ordered-`ENNReal` contractive solver absorbing the coupled internal-loop
inequalities under finite internal and external norms. -/
theorem contractive_ennreal_small_gain_solver
    (E₁ E₂ U₁ U₂ U : ℝ≥0∞)
    (k₁ k₂ β₁ β₂ : ℝ≥0)
    (h_small : SmallGainCondition k₁ k₂)
    (hE₁ : E₁ ≤ U₁ + ((k₂ : ℝ≥0∞) * E₂ + β₂))
    (hE₂ : E₂ ≤ U₂ + ((k₁ : ℝ≥0∞) * E₁ + β₁))
    (hU₁ : U₁ ≤ U)
    (hU₂ : U₂ ≤ U)
    (hE₁_ne_top : E₁ ≠ ⊤)
    (hE₂_ne_top : E₂ ≠ ⊤)
    (hU_ne_top : U ≠ ⊤) :
    ((k₁ : ℝ≥0∞) * E₁ + β₁) +
      ((k₂ : ℝ≥0∞) * E₂ + β₂) ≤
    closedLoopGain k₁ k₂ β₁ β₂ * U +
      closedLoopBias k₁ k₂ β₁ β₂ := by
  have hU₁_ne_top : U₁ ≠ ⊤ := by
    intro htop
    have : (⊤ : ℝ≥0∞) ≤ U := by simpa [htop] using hU₁
    exact hU_ne_top (top_unique this)
  have hU₂_ne_top : U₂ ≠ ⊤ := by
    intro htop
    have : (⊤ : ℝ≥0∞) ≤ U := by simpa [htop] using hU₂
    exact hU_ne_top (top_unique this)
  have hE₁_nn :
      E₁.toNNReal ≤ U₁.toNNReal + (k₂ * E₂.toNNReal + β₂) := by
    have hmono := ENNReal.toNNReal_mono
      (ennreal_finite_rhs₁_ne_top E₂ U₁ k₂ β₂ hU₁_ne_top hE₂_ne_top)
      hE₁
    rw [ennreal_finite_rhs₁_toNNReal E₂ U₁ k₂ β₂ hU₁_ne_top hE₂_ne_top] at hmono
    exact hmono
  have hE₂_nn :
      E₂.toNNReal ≤ U₂.toNNReal + (k₁ * E₁.toNNReal + β₁) := by
    have hmono := ENNReal.toNNReal_mono
      (ennreal_finite_rhs₂_ne_top E₁ U₂ k₁ β₁ hU₂_ne_top hE₁_ne_top)
      hE₂
    rw [ennreal_finite_rhs₂_toNNReal E₁ U₂ k₁ β₁ hU₂_ne_top hE₁_ne_top] at hmono
    exact hmono
  have hU₁_nn : U₁.toNNReal ≤ U.toNNReal :=
    ENNReal.toNNReal_mono hU_ne_top hU₁
  have hU₂_nn : U₂.toNNReal ≤ U.toNNReal :=
    ENNReal.toNNReal_mono hU_ne_top hU₂
  have hE₁_toU :
      E₁.toNNReal ≤ U.toNNReal + (k₂ * E₂.toNNReal + β₂) :=
    le_trans hE₁_nn (add_le_add hU₁_nn (le_refl _))
  have hE₂_toU :
      E₂.toNNReal ≤ U.toNNReal + (k₁ * E₁.toNNReal + β₁) :=
    le_trans hE₂_nn (add_le_add hU₂_nn (le_refl _))
  have hnn :=
    nnreal_small_gain_core_division
      E₁.toNNReal E₂.toNNReal U.toNNReal k₁ k₂ β₁ β₂
      h_small hE₁_toU hE₂_toU
  have h_lhs_ne_top :
      ((k₁ : ℝ≥0∞) * E₁ + β₁) + ((k₂ : ℝ≥0∞) * E₂ + β₂) ≠ ⊤ := by
    rw [← ENNReal.coe_toNNReal hE₁_ne_top,
        ← ENNReal.coe_toNNReal hE₂_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add,
        ← ENNReal.coe_add]
    exact ENNReal.coe_ne_top
  have h_rhs_ne_top :
      closedLoopGain k₁ k₂ β₁ β₂ * U +
        closedLoopBias k₁ k₂ β₁ β₂ ≠ ⊤ := by
    rw [← ENNReal.coe_toNNReal hU_ne_top,
        ← ENNReal.coe_mul,
        ← ENNReal.coe_add]
    exact ENNReal.coe_ne_top
  rw [← ENNReal.toNNReal_le_toNNReal h_lhs_ne_top h_rhs_ne_top]
  rw [ennreal_final_lhs_toNNReal E₁ E₂ k₁ k₂ β₁ β₂ hE₁_ne_top hE₂_ne_top]
  rw [ennreal_final_rhs_toNNReal U k₁ k₂ β₁ β₂ hU_ne_top]
  simpa [closedLoopGain, closedLoopBias] using hnn


/-- A closed loop with all explicit data required by the small-gain theorem
surface.

This packages selector causality, component causality, component finite-gain
certificates, and the small-gain condition.  The actual theorem-level finite-gain
closure remains `closedLoop.isFiniteGainStable`. -/
structure certifiedSmallGainClosedLoop
    (f₁ : (α → E) → α → F)
    (f₂ : (α → F) → α → E)
    (s : ι → Set α)
    (p : ℝ≥0∞)
    (μ : Measure α)
    (k₁ k₂ β₁ β₂ : ℝ≥0) where
  toClosedLoop : closedLoop f₁ f₂ p μ
  measurableSet : ∀ t, MeasurableSet (s t)
  e₁_isCausal :
    (fun u : α → E × F =>
      toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ
  e₂_isCausal :
    (fun u : α → E × F =>
      toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ
  f₁_isCausal : f₁.IsCausal s p μ
  f₂_isCausal : f₂.IsCausal s p μ
  f₁_isFiniteGainStableWith : f₁.IsFiniteGainStableWith k₁ β₁ s p μ
  f₂_isFiniteGainStableWith : f₂.IsFiniteGainStableWith k₂ β₂ s p μ
  out_fst_embedding_aestronglyMeasurable :
    ∀ t u,
      AEStronglyMeasurable
        ((fun x => ((closedLoop.out toClosedLoop u x).1, (0 : E))) : α → F × E)
        (μ.restrict (s t))
  out_snd_embedding_aestronglyMeasurable :
    ∀ t u,
      AEStronglyMeasurable
        ((fun x => ((0 : F), (closedLoop.out toClosedLoop u x).2)) : α → F × E)
        (μ.restrict (s t))
  internal_signal_to_external_eLpNorm_bound :
    ∀ t u, MemLpLoc u p μ →
      (k₁ * eLpNorm (toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) + β₁) +
      (k₂ * eLpNorm (toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) + β₂) ≤
      closedLoopGain k₁ k₂ β₁ β₂ * eLpNorm u p (μ.restrict (s t)) +
        closedLoopBias k₁ k₂ β₁ β₂
  internal_e₁_ne_top :
    ∀ (t : ι) (u : α → E × F), MemLpLoc u p μ →
      eLpNorm (toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≠ ⊤
  internal_e₂_ne_top :
    ∀ (t : ι) (u : α → E × F), MemLpLoc u p μ →
      eLpNorm (toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≠ ⊤
  external_eLpNorm_ne_top :
    ∀ (t : ι) (u : α → E × F), MemLpLoc u p μ →
      eLpNorm u p (μ.restrict (s t)) ≠ ⊤
  p_ge_one : 1 ≤ p
  smallGain : SmallGainCondition k₁ k₂

namespace certifiedSmallGainClosedLoop

/-- The certified small-gain surface exposes the underlying selector-causality
well-posed closed-loop object. -/
def toWellPosedClosedLoop
    (l : certifiedSmallGainClosedLoop f₁ f₂ s p μ k₁ k₂ β₁ β₂) :
    wellPosedClosedLoop f₁ f₂ s p μ where
  toClosedLoop := l.toClosedLoop
  e₁_isCausal := l.e₁_isCausal
  e₂_isCausal := l.e₂_isCausal

/-- The certified small-gain surface exposes closed-loop causality. -/
theorem isCausal
    (l : certifiedSmallGainClosedLoop f₁ f₂ s p μ k₁ k₂ β₁ β₂) :
    (closedLoop.out l.toClosedLoop).IsCausal s p μ :=
  closedLoop.isCausal l.toClosedLoop
    l.measurableSet
    l.e₁_isCausal
    l.e₂_isCausal
    l.f₁_isCausal
    l.f₂_isCausal
end certifiedSmallGainClosedLoop

theorem closedLoop.isFiniteGainStable
    (l : closedLoop f₁ f₂ p μ)
    (_hs : ∀ t, MeasurableSet (s t))
    (_he₁ :
      (fun u : α → E × F =>
        l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (_he₂ :
      (fun u : α → E × F =>
        l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (_hf₁_causal : f₁.IsCausal s p μ)
    (_hf₂_causal : f₂.IsCausal s p μ)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ)
    (hout₁ :
      ∀ t u,
        AEStronglyMeasurable
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          (μ.restrict (s t)))
    (hout₂ :
      ∀ t u,
        AEStronglyMeasurable
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (_h_small : SmallGainCondition k₁ k₂)
    (h_internal_signal_to_external_eLpNorm_bound :
      ∀ t u, MemLpLoc u p μ →
        (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₁) +
        (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₂) ≤
        closedLoopGain k₁ k₂ β₁ β₂ * eLpNorm u p (μ.restrict (s t)) +
          closedLoopBias k₁ k₂ β₁ β₂) :
    (closedLoop.out l).IsFiniteGainStableWith (closedLoopGain k₁ k₂ β₁ β₂)
      (closedLoopBias k₁ k₂ β₁ β₂) s p μ := by
  constructor
  · intro u hu
    rw [memLpLoc_prod_iff] at hu ⊢
    constructor
    · apply hf₁.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).1
    · apply hf₂.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).2
  · intro t u hu
    have hu_components :
        MemLpLoc (fun x => (u x).1) p μ ∧
        MemLpLoc (fun x => (u x).2) p μ := by
      simpa [memLpLoc_prod_iff] using hu
    have hinternal_memLpLoc :
        MemLpLoc (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) p μ ∧
        MemLpLoc (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) p μ :=
      l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu_components
    have hprod_split :
        eLpNorm (closedLoop.out l u) p (μ.restrict (s t)) ≤
          eLpNorm
            ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
            p (μ.restrict (s t)) +
          eLpNorm
            ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
            p (μ.restrict (s t)) := by
      exact eLpNorm_prod_le_embedded_fst_add_embedded_snd
        (hout₁ t u) (hout₂ t u) hp
    rcases hf₁ with ⟨_, hf₁_bound⟩
    rcases hf₂ with ⟨_, hf₂_bound⟩
    have hf₁_component_bound :=
      hf₁_bound t (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) hinternal_memLpLoc.1
    have hf₂_component_bound :=
      hf₂_bound t (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) hinternal_memLpLoc.2
    have hfst_closedLoop_coordinate :
        (fun x => (closedLoop.out l u x).1) =
          f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) := by
      funext x
      exact closedLoop.out_fst l u x
    have hsnd_closedLoop_coordinate :
        (fun x => (closedLoop.out l u x).2) =
          f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) := by
      funext x
      exact closedLoop.out_snd l u x
    have hf₁_closedLoop_coordinate_bound :
        eLpNorm (fun x => (closedLoop.out l u x).1) p (μ.restrict (s t)) ≤
          k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t)) + β₁ := by
      simpa [hfst_closedLoop_coordinate] using hf₁_component_bound
    have hf₂_closedLoop_coordinate_bound :
        eLpNorm (fun x => (closedLoop.out l u x).2) p (μ.restrict (s t)) ≤
          k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)) p (μ.restrict (s t)) + β₂ := by
      simpa [hsnd_closedLoop_coordinate] using hf₂_component_bound
    have hfst_embedded_le_coordinate :
        eLpNorm
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          p (μ.restrict (s t)) ≤
        eLpNorm (fun x => (closedLoop.out l u x).1) p (μ.restrict (s t)) :=
      eLpNorm_embedded_fst_le_coordinate
    have hsnd_embedded_le_coordinate :
        eLpNorm
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          p (μ.restrict (s t)) ≤
        eLpNorm (fun x => (closedLoop.out l u x).2) p (μ.restrict (s t)) :=
      eLpNorm_embedded_snd_le_coordinate
    have hfst_embedded_bound :
        eLpNorm
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          p (μ.restrict (s t)) ≤
          k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁ :=
      le_trans hfst_embedded_le_coordinate hf₁_closedLoop_coordinate_bound
    have hsnd_embedded_bound :
        eLpNorm
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          p (μ.restrict (s t)) ≤
          k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂ :=
      le_trans hsnd_embedded_le_coordinate hf₂_closedLoop_coordinate_bound
    have hsum_embedded_bound :
        eLpNorm
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          p (μ.restrict (s t)) +
        eLpNorm
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          p (μ.restrict (s t)) ≤
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂) :=
      add_le_add hfst_embedded_bound hsnd_embedded_bound
    have hclosedLoop_raw_bound :
        eLpNorm (closedLoop.out l u) p (μ.restrict (s t)) ≤
          (k₁ * eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₁) +
          (k₂ * eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
            p (μ.restrict (s t)) + β₂) :=
      le_trans hprod_split hsum_embedded_bound
    exact le_trans hclosedLoop_raw_bound
      (h_internal_signal_to_external_eLpNorm_bound t u hu)

namespace certifiedSmallGainClosedLoop

/-- Derive the certified internal-signal bound by instantiating the isolated
ordered-`ENNReal` contractive small-gain solver with the certified finiteness
fields. -/
theorem internal_signal_to_external_eLpNorm_bound_from_contract_solver
    (l : certifiedSmallGainClosedLoop f₁ f₂ s p μ k₁ k₂ β₁ β₂)
    (t : ι)
    (u : α → E × F)
    (hu : MemLpLoc u p μ)
    (hu₁_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.fst ∘ u) (μ.restrict (s t)))
    (hu₂_aestronglyMeasurable :
      AEStronglyMeasurable (Prod.snd ∘ u) (μ.restrict (s t)))
    (hf₁_e₁_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₁ (l.toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t)))
    (hf₂_e₂_aestronglyMeasurable :
      AEStronglyMeasurable
        (f₂ (l.toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
        (μ.restrict (s t))) :
    (k₁ * eLpNorm (l.toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₁) +
    (k₂ * eLpNorm (l.toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
      p (μ.restrict (s t)) + β₂) ≤
      closedLoopGain k₁ k₂ β₁ β₂ * eLpNorm u p (μ.restrict (s t)) +
        closedLoopBias k₁ k₂ β₁ β₂ := by
  have hE₁ :
      eLpNorm (l.toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≤
      eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) +
        (k₂ * eLpNorm
          (l.toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₂) :=
    l.toClosedLoop.internal_e₁_bound_from_loop
      t u hu hu₁_aestronglyMeasurable hf₂_e₂_aestronglyMeasurable
      l.p_ge_one l.f₂_isFiniteGainStableWith
  have hE₂ :
      eLpNorm (l.toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)) ≤
      eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) +
        (k₁ * eLpNorm
          (l.toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)) + β₁) :=
    l.toClosedLoop.internal_e₂_bound_from_loop
      t u hu hu₂_aestronglyMeasurable hf₁_e₁_aestronglyMeasurable
      l.p_ge_one l.f₁_isFiniteGainStableWith
  have hU₁ :
      eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)) ≤
        eLpNorm u p (μ.restrict (s t)) := by
    exact eLpNorm_mono (fun x => norm_fst_le (u x))
  have hU₂ :
      eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)) ≤
        eLpNorm u p (μ.restrict (s t)) := by
    exact eLpNorm_mono (fun x => norm_snd_le (u x))
  exact contractive_ennreal_small_gain_solver
    (E₁ :=
      eLpNorm (l.toClosedLoop.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)))
    (E₂ :=
      eLpNorm (l.toClosedLoop.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
        p (μ.restrict (s t)))
    (U₁ := eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)))
    (U₂ := eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)))
    (U := eLpNorm u p (μ.restrict (s t)))
    (k₁ := k₁)
    (k₂ := k₂)
    (β₁ := β₁)
    (β₂ := β₂)
    l.smallGain
    hE₁
    hE₂
    hU₁
    hU₂
    (l.internal_e₁_ne_top t u hu)
    (l.internal_e₂_ne_top t u hu)
    (l.external_eLpNorm_ne_top t u hu)

/-- The certified small-gain surface exposes the finite-gain theorem through
the current `closedLoop.isFiniteGainStable` theorem surface. -/
theorem isFiniteGainStable
    (l : certifiedSmallGainClosedLoop f₁ f₂ s p μ k₁ k₂ β₁ β₂) :
    (closedLoop.out l.toClosedLoop).IsFiniteGainStableWith
      (closedLoopGain k₁ k₂ β₁ β₂)
      (closedLoopBias k₁ k₂ β₁ β₂) s p μ :=
  closedLoop.isFiniteGainStable l.toClosedLoop
    l.measurableSet
    l.e₁_isCausal
    l.e₂_isCausal
    l.f₁_isCausal
    l.f₂_isCausal
    l.f₁_isFiniteGainStableWith
    l.f₂_isFiniteGainStableWith
    l.out_fst_embedding_aestronglyMeasurable
    l.out_snd_embedding_aestronglyMeasurable
    l.p_ge_one
    l.smallGain
    l.internal_signal_to_external_eLpNorm_bound

end certifiedSmallGainClosedLoop

/-- Direct closed-loop finite-gain theorem using the contractive small-gain
solver, without requiring the `certifiedSmallGainClosedLoop` convenience wrapper.

The boundedness hypothesis turns `MemLpLoc` into the `MemLp` finiteness witnesses
required by the raw ENNReal solver on each restricted set `s t`. -/
theorem closedLoop.isFiniteGainStable_from_contract_solver_direct
    {ι : Type u_1}
    {α : Type u_2}
    {E : Type u_5}
    {F : Type u_8}
    {m : MeasurableSpace α}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [Bornology α]
    {β₁ β₂ k₁ k₂ : NNReal}
    {f₁ : (α → E) → α → F}
    {f₂ : (α → F) → α → E}
    {s : ι → Set α}
    {p : ENNReal}
    {μ : Measure α}
    (l : closedLoop f₁ f₂ p μ)
    (hs : ∀ t, MeasurableSet (s t))
    (hs_bounded : ∀ t, Bornology.IsBounded (s t))
    (he₁ :
      (fun u : α → E × F =>
        l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (he₂ :
      (fun u : α → E × F =>
        l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (hf₁_causal : f₁.IsCausal s p μ)
    (hf₂_causal : f₂.IsCausal s p μ)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ)
    (hout₁ :
      ∀ t (u : α → E × F),
        AEStronglyMeasurable
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          (μ.restrict (s t)))
    (hout₂ :
      ∀ t (u : α → E × F),
        AEStronglyMeasurable
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          (μ.restrict (s t)))
    (hu₁_aestronglyMeasurable :
      ∀ t (u : α → E × F), MemLpLoc u p μ →
        AEStronglyMeasurable (Prod.fst ∘ u) (μ.restrict (s t)))
    (hu₂_aestronglyMeasurable :
      ∀ t (u : α → E × F), MemLpLoc u p μ →
        AEStronglyMeasurable (Prod.snd ∘ u) (μ.restrict (s t)))
    (hf₁_e₁_aestronglyMeasurable :
      ∀ t (u : α → E × F), MemLpLoc u p μ →
        AEStronglyMeasurable
          (f₁ (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)))
          (μ.restrict (s t)))
    (hf₂_e₂_aestronglyMeasurable :
      ∀ t (u : α → E × F), MemLpLoc u p μ →
        AEStronglyMeasurable
          (f₂ (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)))
          (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (h_small : SmallGainCondition k₁ k₂) :
    (closedLoop.out l).IsFiniteGainStableWith
      (closedLoopGain k₁ k₂ β₁ β₂)
      (closedLoopBias k₁ k₂ β₁ β₂) s p μ :=
  closedLoop.isFiniteGainStable l
    hs he₁ he₂ hf₁_causal hf₂_causal hf₁ hf₂ hout₁ hout₂ hp h_small
    (fun t u hu =>
      have hu_components :
          MemLpLoc (Prod.fst ∘ u) p μ ∧
          MemLpLoc (Prod.snd ∘ u) p μ := by
        simpa [memLpLoc_prod_iff] using hu
      have hinternal :=
        l.memLpLoc (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
      contractive_ennreal_small_gain_solver
        (E₁ := eLpNorm (l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)))
        (E₂ := eLpNorm (l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u))
          p (μ.restrict (s t)))
        (U₁ := eLpNorm (Prod.fst ∘ u) p (μ.restrict (s t)))
        (U₂ := eLpNorm (Prod.snd ∘ u) p (μ.restrict (s t)))
        (U := eLpNorm u p (μ.restrict (s t)))
        (k₁ := k₁)
        (k₂ := k₂)
        (β₁ := β₁)
        (β₂ := β₂)
        h_small
        (l.internal_e₁_bound_from_loop
          t u hu
          (hu₁_aestronglyMeasurable t u hu)
          (hf₂_e₂_aestronglyMeasurable t u hu)
          hp hf₂)
        (l.internal_e₂_bound_from_loop
          t u hu
          (hu₂_aestronglyMeasurable t u hu)
          (hf₁_e₁_aestronglyMeasurable t u hu)
          hp hf₁)
        (eLpNorm_mono (fun x => norm_fst_le (u x)))
        (eLpNorm_mono (fun x => norm_snd_le (u x)))
        ((hinternal.1 (s t) ⟨hs t, hs_bounded t⟩).eLpNorm_ne_top)
        ((hinternal.2 (s t) ⟨hs t, hs_bounded t⟩).eLpNorm_ne_top)
        ((hu (s t) ⟨hs t, hs_bounded t⟩).eLpNorm_ne_top))

/-- Conditional uniqueness surface for internal closed-loop signals.

This does not assert that closed-loop internal equations are uniquely solvable.
It isolates the exact missing hypothesis: for every external input `u`, the
chosen internal equation has a unique solution. -/
theorem closedLoop.internalSignals_unique_of_unique_internal_equation
    {α : Type u_2}
    {E : Type u_5}
    {F : Type u_8}
    {_m : MeasurableSpace α}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [Bornology α]
    {p : ENNReal}
    {μ : Measure α}
    {f₁ : (α → E) → α → F}
    {f₂ : (α → F) → α → E}
    (_l : closedLoop f₁ f₂ p μ)
    (ClosedLoopInternalEquation :
      (α → E × F) → ((α → F) × (α → E)) → Prop)
    (hunique :
      ∀ u, ∃! z : (α → F) × (α → E),
        ClosedLoopInternalEquation u z)
    (u : α → E × F)
    {z z' : (α → F) × (α → E)}
    (hz : ClosedLoopInternalEquation u z)
    (hz' : ClosedLoopInternalEquation u z') :
    z = z' := by
  obtain ⟨_, _, huniq⟩ := hunique u
  exact (huniq z hz).trans ((huniq z' hz').symm)

/-- Sharper direct closed-loop finite-gain theorem: derives the four internal
AEStronglyMeasurable witnesses from `MemLpLoc`, component finite-gain stability,
and bounded local windows. -/
theorem closedLoop.isFiniteGainStable_from_contract_solver_direct_derived_meas
    {ι : Type u_1}
    {α : Type u_2}
    {E : Type u_5}
    {F : Type u_8}
    {m : MeasurableSpace α}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [Bornology α]
    {β₁ β₂ k₁ k₂ : NNReal}
    {f₁ : (α → E) → α → F}
    {f₂ : (α → F) → α → E}
    {s : ι → Set α}
    {p : ENNReal}
    {μ : Measure α}
    (l : closedLoop f₁ f₂ p μ)
    (hs : ∀ t, MeasurableSet (s t))
    (hs_bounded : ∀ t, Bornology.IsBounded (s t))
    (he₁ :
      (fun u : α → E × F =>
        l.e₁ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (he₂ :
      (fun u : α → E × F =>
        l.e₂ (Prod.fst ∘ u) (Prod.snd ∘ u)).IsCausal s p μ)
    (hf₁_causal : f₁.IsCausal s p μ)
    (hf₂_causal : f₂.IsCausal s p μ)
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ)
    (hout₁ :
      ∀ t (u : α → E × F),
        AEStronglyMeasurable
          ((fun x => ((closedLoop.out l u x).1, (0 : E))) : α → F × E)
          (μ.restrict (s t)))
    (hout₂ :
      ∀ t (u : α → E × F),
        AEStronglyMeasurable
          ((fun x => ((0 : F), (closedLoop.out l u x).2)) : α → F × E)
          (μ.restrict (s t)))
    (hp : 1 ≤ p)
    (h_small : SmallGainCondition k₁ k₂) :
    (closedLoop.out l).IsFiniteGainStableWith
      (closedLoopGain k₁ k₂ β₁ β₂)
      (closedLoopBias k₁ k₂ β₁ β₂) s p μ :=
  closedLoop.isFiniteGainStable_from_contract_solver_direct l
    hs hs_bounded he₁ he₂ hf₁_causal hf₂_causal hf₁ hf₂ hout₁ hout₂
    (fun t u hu => by
      have hu_components :
          MemLpLoc (Prod.fst ∘ u) p μ ∧
          MemLpLoc (Prod.snd ∘ u) p μ := by
        simpa [memLpLoc_prod_iff] using hu
      exact (hu_components.1 (s t) ⟨hs t, hs_bounded t⟩).aestronglyMeasurable)
    (fun t u hu => by
      have hu_components :
          MemLpLoc (Prod.fst ∘ u) p μ ∧
          MemLpLoc (Prod.snd ∘ u) p μ := by
        simpa [memLpLoc_prod_iff] using hu
      exact (hu_components.2 (s t) ⟨hs t, hs_bounded t⟩).aestronglyMeasurable)
    (fun t u hu => by
      have hu_components :
          MemLpLoc (Prod.fst ∘ u) p μ ∧
          MemLpLoc (Prod.snd ∘ u) p μ := by
        simpa [memLpLoc_prod_iff] using hu
      have hinternal :=
        l.memLpLoc (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
      exact ((hf₁.memLpLoc hinternal.1) (s t) ⟨hs t, hs_bounded t⟩).aestronglyMeasurable)
    (fun t u hu => by
      have hu_components :
          MemLpLoc (Prod.fst ∘ u) p μ ∧
          MemLpLoc (Prod.snd ∘ u) p μ := by
        simpa [memLpLoc_prod_iff] using hu
      have hinternal :=
        l.memLpLoc (Prod.fst ∘ u) (Prod.snd ∘ u) hu_components
      exact ((hf₂.memLpLoc hinternal.2) (s t) ⟨hs t, hs_bounded t⟩).aestronglyMeasurable)
    hp h_small

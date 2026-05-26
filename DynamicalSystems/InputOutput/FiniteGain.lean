/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence

/- # Causal operators and finite gain

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

instance : MeasureSpace ℝ≥0 where
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

theorem closedLoop.isCausal (l : closedLoop f₁ f₂ p μ) (hf₁ : IsCausal f₁ s p μ)
  (hf₂ : IsCausal f₂ s p μ) :
    IsCausal (closedLoop.out l) s p μ := by
  constructor
  · intro u hu
    rw [memLpLoc_prod_iff] at hu ⊢
    constructor
    · apply hf₁.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).1
    · apply hf₂.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).2
  · intro t u hu
    sorry

/-- foo -/
def closedLoopBias (k₁ k₂ β₁ β₂ : ℝ≥0) : ℝ≥0 := sorry

/-- foo -/
def closedLoopGain (k₁ k₂ β₁ β₂ : ℝ≥0) : ℝ≥0 := sorry

theorem closedLoop.isFiniteGainStable (l : closedLoop f₁ f₂ p μ)
  (hf₁_causal : IsCausal f₁ s p μ)
  (hf₂_causal : IsCausal f₂ s p μ)
  (hf₁ : IsFiniteGainStableWith f₁ k₁ β₁ s p μ)
  (hf₂ : IsFiniteGainStableWith f₂ k₂ β₂ s p μ) (hk : k₁ * k₂ < 1) :
    IsFiniteGainStableWith (closedLoop.out l)  (closedLoopGain k₁ k₂ β₁ β₂)
      (closedLoopBias k₁ k₂ β₁ β₂) s p μ := by
  constructor
  · intro u hu
    rw [memLpLoc_prod_iff] at hu ⊢
    constructor
    · apply hf₁.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).1
    · apply hf₂.memLpLoc
      exact (l.memLpLoc (fun x ↦ (u x).1) (fun x ↦ (u x).2) hu).2
  · intro t u
    sorry

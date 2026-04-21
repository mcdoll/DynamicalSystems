/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.LaSalle
public import DynamicalSystems.Stability.Lyapunov
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
--public import Mathlib.Analysis.Calculus.MeanValue

/-! # Asymptotic stability of the RLC circuit

In this file, we prove that the RLC circuit is asymptotic stable. -/

@[expose] public noncomputable section

variable {f g : ℝ → ℝ}
variable (hf : Continuous f) (hg : Continuous g) (hf_pass : ∀ x, 0 ≤ x * f x)
  (hg_pass : ∀ x, 0 ≤ x * g x)

-- maybe define a structure for locally passive functions

theorem integral_hasDerivAt (hf : Continuous f) (a b) :
    HasDerivAt (fun x : ℝ ↦ ∫ y in a..x, f y) (f b) b := by
  apply (intervalIntegral.integral_hasStrictDerivAt_right _ _ _).hasDerivAt
  -- Todo: all three should be `fun_prop`
  · exact Continuous.intervalIntegrable hf a b
  · exact Continuous.stronglyMeasurableAtFilter hf MeasureTheory.volume (nhds b)
  fun_prop

-- should be in mathlib? specialize this t₀ t₁
@[fun_prop]
theorem integral_differentiableAt (hf : Continuous f) (a) :
    Differentiable ℝ (fun x : ℝ ↦ ∫ y in a..x, f y) := by
  intro x
  exact (integral_hasDerivAt hf a x).differentiableAt

variable {μ : MeasureTheory.Measure ℝ} {a b : ℝ}

-- should be in mathlib
theorem integral_nonneg_of_Ioo [MeasureTheory.NoAtoms μ] (hab : a ≤ b)
    (hf : IntervalIntegrable f μ a b) (h : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    0 ≤ ∫ u in a..b, f u ∂μ := by
  convert intervalIntegral.integral_mono_on_of_le_Ioo hab _ hf h
  · simp
  · simp [intervalIntegrable_const_iff]

namespace RLCCircuit

variable (g) in
/-- The Lyapunov function is given by `x ^ 2 / 2 + ∫ t in 0..x, g t`. -/
protected def energy (x : ℝ × ℝ) : ℝ := 2⁻¹ * x.2 ^ 2 + ∫ t in 0..x.1, g t

@[fun_prop]
theorem differentiable_energy (hg : Continuous g) : Differentiable ℝ (RLCCircuit.energy g) := by
  unfold RLCCircuit.energy
  fun_prop

theorem nonneg_energy (hg : Continuous g) (hg_pass : ∀ x, 0 ≤ x * g x) (x) :
    0 ≤ RLCCircuit.energy g x := by
  have : 0 ≤ ∫ t in 0..x.1, g t := by
    by_cases! hx : 0 ≤ x.1
    · apply integral_nonneg_of_Ioo hx
      · -- should be `fun_prop`
        exact IntervalIntegrable.symm (Continuous.intervalIntegrable hg x.1 0)
      intro y ⟨hy₁, hy₂⟩
      exact nonneg_of_mul_nonneg_right (hg_pass y) hy₁
    · -- similar argument
      sorry
  unfold RLCCircuit.energy
  positivity

theorem fderiv_energy (hg : Continuous g) (x) :
    fderiv ℝ (RLCCircuit.energy g) x = x.2 • .snd ℝ ℝ ℝ + g x.1 • .fst ℝ ℝ ℝ := by
  unfold RLCCircuit.energy
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_const_mul (by fun_prop), fderiv_pow _ (by fun_prop), fderiv_snd]
  --rw [smul_eq_mul]
  simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, ← smul_assoc, smul_eq_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel_left₀, add_right_inj]
  calc
    _ = fderiv ℝ ((fun x ↦ ∫ (t : ℝ) in 0..x, g t) ∘ Prod.fst) x := by rfl
    _ = (fderiv ℝ (fun x ↦ ∫ (t : ℝ) in 0..x, g t) x.1).comp (ContinuousLinearMap.fst _ _ _) := by
      rw [← fderiv_fst (p := x)]
      exact fderiv_comp x (by fun_prop) (by fun_prop)
    _ = _ := by
      ext
      · simp [hg.deriv_integral _ 0 x.1]
      · simp

protected
theorem isLinearlyBddVectorField {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f)
    (hf₂ : ∀ x, |deriv f x| ≤ C₁) (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) :
    IsLinearlyBddVectorField (fun x : ℝ × ℝ ↦ (x.2, - f x.2 - g x.1)) where
  differentiable := by fun_prop
  exists_bound := by
    simp only [Prod.forall]
    use 1 + C₁ + C₂
    have hC₁ : 0 ≤ C₁ := by sorry
    have hC₂ : 0 ≤ C₂ := by sorry
    have hC' : 0 ≤ 1 + C₁ + C₂ := by sorry
    intro x y
    rw [DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop), fderiv_snd]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop), fderiv_fun_neg]
    apply ContinuousLinearMap.opNorm_le_bound _ hC'
    rintro ⟨x', y'⟩
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.neg_apply, Prod.norm_mk,
      Real.norm_eq_abs, sup_le_iff]
    constructor
    · grw [← Std.right_le_max]
      refine le_mul_of_one_le_left (by positivity) ?_
      rw [add_assoc]
      grw [← hC₁, ← hC₂]
      simp
    · grw [abs_sub]
      rw [abs_neg, add_mul]
      gcongr
      · rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
        simp only [fderiv_snd, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd',
          Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, abs_mul]
        rw [mul_comm]
        gcongr
        · grw [hf₂ y]
          simp
        · simp
      · rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
        simp only [fderiv_fst, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst',
          Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, abs_mul]
        rw [mul_comm]
        gcongr
        · grw [hg₂ x]
        · simp

open Classical in
variable (f g) in
/-- The flow of the vector field `x ↦ r • x`. -/
protected
def flow : Flow ℝ (ℝ × ℝ) :=
  if h : Differentiable ℝ f ∧ Differentiable ℝ g ∧ (∃ C₁, ∀ x, |deriv f x| ≤ C₁) ∧
    ∃ C₂, ∀ x, |deriv g x| ≤ C₂
  then (RLCCircuit.isLinearlyBddVectorField h.1 h.2.2.1.choose_spec h.2.1 h.2.2.2.choose_spec).flow
  else sorry

theorem flow_eq {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f)
    (hf₂ : ∀ x, |deriv f x| ≤ C₁) (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) :
    RLCCircuit.flow f g = (RLCCircuit.isLinearlyBddVectorField hf₁ hf₂ hg₁ hg₂).flow := by
  have h : Differentiable ℝ f ∧ Differentiable ℝ g ∧ (∃ C₁, ∀ x, |deriv f x| ≤ C₁) ∧
      ∃ C₂, ∀ x, |deriv g x| ≤ C₂ := ⟨hf₁, hg₁, ⟨C₁, hf₂⟩, ⟨C₂, hg₂⟩⟩
  simp [RLCCircuit.flow, h]

@[fun_prop]
theorem differentiable_flow (x) : Differentiable ℝ (RLCCircuit.flow f g · x) := by
  by_cases h : Differentiable ℝ f ∧ Differentiable ℝ g ∧ (∃ C₁, ∀ x, |deriv f x| ≤ C₁) ∧
    ∃ C₂, ∀ x, |deriv g x| ≤ C₂
  · simp [RLCCircuit.flow, h]
    sorry
  · simp [RLCCircuit.flow, h]
    sorry

theorem deriv_flow {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f)
    (hf₂ : ∀ x, |deriv f x| ≤ C₁) (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) (t) (x) :
    deriv (RLCCircuit.flow f g · x) t = ((RLCCircuit.flow f g t x).2,
      - f (RLCCircuit.flow f g t x).2 - g (RLCCircuit.flow f g t x).1) := by
  simp [flow_eq hf₁ hf₂ hg₁ hg₂]

/-- The energy function is a Lyapunov function for the RLC system. -/
theorem isLyapunov_energy_flow {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f) (hf₂ : ∀ x, |deriv f x| ≤ C₁)
    (hf_pass : ∀ x, 0 ≤ x * f x)
    (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) (hg_pass : ∀ x, 0 ≤ x * g x) :
    IsLyapunov (RLCCircuit.energy g) (RLCCircuit.flow f g) := by
  have hg : Continuous g := hg₁.continuous
  apply Flow.isLyapunov differentiable_flow (nonneg_energy hg hg_pass) (by fun_prop)
  intro x
  rw [deriv_flow hf₁ hf₂ hg₁ hg₂]
  rw [fderiv_energy hg₁.continuous]
  simp only [Flow.map_zero, id_eq, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_fst']
  ring_nf
  exact neg_nonpos_of_nonneg (hf_pass x.2)

open scoped Topology
open Filter

/-- The origin is stable under the forward flow of `d/dt x = r x` -/
theorem isStableOn_flow {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f) (hf₂ : ∀ x, |deriv f x| ≤ C₁)
    (hf_pass : ∀ x, 0 ≤ x * f x)
    (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) (hg_pass : ∀ x, 0 ≤ x * g x) :
    (𝓝 0).IsStableOn (RLCCircuit.flow f g) (Set.Ici 0) := by
  apply (isLyapunov_energy_flow hf₁ hf₂ hf_pass hg₁ hg₂ hg_pass).isStableOn (by sorry) (by simp)
    zero_lt_one
  --simp only [sq_le_one_iff_abs_le_one]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (differentiable_energy hg₁.continuous).continuous (by fun_prop)
  · sorry

/-- The origin is asymptotic stable under the forward flow of `d/dt x = r x` -/
theorem tendsto_smulFlow {C₁ C₂ : ℝ} (hf₁ : Differentiable ℝ f) (hf₂ : ∀ x, |deriv f x| ≤ C₁)
    (hf_pass : ∀ x, 0 ≤ x * f x) (hf' : ∀ x, x * f x = 0 ↔ x = 0)
    (hg₁ : Differentiable ℝ g) (hg₂ : ∀ x, |deriv g x| ≤ C₂) (hg_pass : ∀ x, 0 ≤ x * g x) (x) :
    Tendsto (RLCCircuit.flow f g · x) atTop (𝓝 0) := by
  apply (isLyapunov_energy_flow hf₁ hf₂ hf_pass hg₁ hg₂ hg_pass).tendsto_of_forall_exists_nonMem
      (isCompact_closedBall 0 ‖x‖)
  · intro y hy
    sorry
  · apply differentiable_energy hg₁.continuous
  · fun_prop
  · intro y hy h
    simp_rw [deriv_flow hf₁ hf₂ hg₁ hg₂, fderiv_energy hg₁.continuous, Flow.map_zero_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_fst']
    ring_nf
    simp_rw [neg_eq_zero, hf', Set.mem_setOf_eq]
    by_contra!
    set γ₁ := fun t ↦ (RLCCircuit.flow f g t y).1
    set γ₂ := fun t ↦ (RLCCircuit.flow f g t y).2
    have hγ₀ : (γ₁ 0, γ₂ 0) = y := by simp [γ₁, γ₂]
    have hγ₁_ode : deriv γ₁ = γ₂ := by
      ext t
      simp only [γ₁, γ₂]
      have := deriv_flow hf₁ hf₂ hg₁ hg₂ t y
      rw [Prod.ext_iff] at this
      simp only at this
      rw [← this.1]
      sorry
    have hγ₂_ode : deriv γ₂ = - f ∘ γ₂ - g ∘ γ₁ := by
      ext t
      simp only [γ₁, γ₂]
      simp only [Pi.sub_apply, Pi.neg_apply, Function.comp_apply]
      have := deriv_flow hf₁ hf₂ hg₁ hg₂ t y
      simp only [Prod.ext_iff] at this
      rw [← this.2]
      sorry
    have hγ₂ : ∀ t ≥ 0, γ₂ t = 0 := by
      intro t ht
      simp [γ₂, this t ht]
    have hx : ∃ c, ∀ t ≥ 0, γ₁ t = c := by
      use γ₂ 0
      intro t ht
      -- use ftc
      sorry
    obtain ⟨c, hc⟩ := hx
    have hy' : ∀ t ≥ 0, deriv γ₂ t = - g c := by
      intro t ht
      simp [hγ₂_ode, hγ₂ t ht, hc t ht]
      sorry
    have hγ₂' : ∀ t ≥ 0, deriv γ₂ t = 0 := by
      -- follows from hγ₂
      sorry
    have hgc : g c = 0 := by
      rw [← neg_eq_zero, ← hγ₂' 0 (le_refl _), hy' 0 (le_refl _)]
    have hc' : c = 0 := by
      -- passivity
      sorry
    apply h
    rw [← hγ₀, hγ₂ 0 (le_refl _), hc 0 (le_refl _), hc']
    rfl

-- the energy is decreasing along the flow

end RLCCircuit

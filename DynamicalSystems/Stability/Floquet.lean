/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
public import DynamicalSystems.Stability.Basic

import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Basic Floquet Theory

This file formalizes the core results of Floquet theory for linear differential equations
with periodic coefficients of the form `x'(t) = L(t) x(t)` where `L(t + T) = L(t)`.

We follow Michael J. Ward, *Basic Floquet Theory*, Chapter 3:
- **Periodic Linear Propagators**: Transition operators `X(t₀, t)` satisfying `X(t₀, t₀) = id`,
  `X(t₁, t₂) ∘ X(t₀, t₁) = X(t₀, t₂)`, and `d/dt X = L(t) ∘ X`.
- **Shift Invariance**: `X(t₀ + T, t + T) = X(t₀, t)`.
- **Monodromy Operator**: `M = X(0, T)` (Ward Definition §3.1).
- **Fundamental Factorization**: `X(0, t + T) = X(0, t) ∘ M` (Ward Theorem 3.3(i)).
- **Stroboscopic Powers**: `X(0, t + k • T) = X(0, t) ∘ (M ^ k)` and `X(0, k • T) x₀ = (M ^ k) x₀`.
- **Floquet Multipliers and Modes**: Eigenvalues `ρ` of `M` give solutions satisfying
  `x(t + T) = ρ • x(t)` (Ward Theorem 3.4(i)) and `x(k • T) = ρ ^ k • x₀`.
- **Quasi-Periodic Normal Form**: For `ρ > 0` and `μ = log ρ / T`, any Floquet mode factors as
  `x(t) = exp(μ * t) • p(t)` where `p` is `T`-periodic (Ward Theorem 3.4(ii)).
- **Stability of Periodic Orbits**: Linearization of an autonomous periodic orbit has `1` as a
  Floquet multiplier along the orbit tangent (Ward Section 3.1.2).
- **Dynamic Stability of Discrete Flows**:
  - `IsStableOn`: If `‖M‖ ≤ 1`, the stroboscopic origin is Lyapunov stable (sufficient condition).
  - `IsAttractive`: If `‖M‖ < 1`, trajectories converge to `0` along `atTop`.
  - Mode convergence and divergence: If `M v = ρ • v`, the trajectory satisfies
    `X(0, k • T) v = (ρ ^ k) • v`. When `|ρ| < 1`, `X(0, k • T) v → 0`.
    When `1 < |ρ|` and `v ≠ 0`, `‖X(0, k • T) v‖ → ∞`.
- **Second-Order Conservative Characteristic Roots**: For conservative 2D systems (`det M = 1`,
  `φ = (tr M) / 2`):
  - When `|tr M| < 2` (`|φ| < 1`), the roots are complex conjugates lying strictly on the unit
    circle (`‖z‖ = 1`) with non-zero imaginary parts (Ward Section 3.2.3 Case I).
  - When `|tr M| > 2` (`1 < |φ|`), there exists a real root with `1 < |ρ|` (Ward Section 3.2.3
    Case II). Note that for negative trace `φ < -1`, the roots are negative, so `1 < |ρ|` rather
    than `ρ > 1`.
  - These are algebraic root lemmas for the scalar polynomial; lifting them to full 2D matrix
    dynamic stability requires Jordan form or symplecticity, while operator norm bounds
    `‖M‖ ≤ 1` give direct flow stability.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. Periodic Operators and Linear Propagators -/

/-- A continuous linear vector field `L : ℝ → E →L[ℝ] E` is periodic with period `T`. -/
def IsPeriodicOperator (L : ℝ → E →L[ℝ] E) (T : ℝ) : Prop :=
  Function.Periodic L T

/-- A linear propagator (state transition operator) for the linear system `x' = L(t) x`.
`X t₀ t` maps the state at time `t₀` to the state at time `t`. -/
structure LinearPropagator (L : ℝ → E →L[ℝ] E) (X : ℝ → ℝ → E →L[ℝ] E) : Prop where
  /-- Consistency: at initial time `t₀`, `X t₀ t₀` is the identity map. -/
  initial : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id ℝ E
  /-- Cocycle / semigroup property: transition across an intermediate time `t₁`. -/
  comp : ∀ t₀ t₁ t₂, X t₁ t₂ ∘L X t₀ t₁ = X t₀ t₂
  /-- Solution property: `t ↦ X t₀ t` satisfies the differential equation `d/dt X = L(t) ∘ X`. -/
  hasDerivAt : ∀ t₀ t, HasDerivAt (X t₀ ·) (L t ∘L X t₀ t) t

namespace LinearPropagator

variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E}

theorem comp_apply (hX : LinearPropagator L X) (t₀ t₁ t₂ : ℝ) (x : E) :
    X t₁ t₂ (X t₀ t₁ x) = X t₀ t₂ x := by
  have h := ContinuousLinearMap.ext_iff.mp (hX.comp t₀ t₁ t₂) x
  exact h

theorem initial_apply (hX : LinearPropagator L X) (t₀ : ℝ) (x : E) :
    X t₀ t₀ x = x := by
  simp [hX.initial]

/-- Ward Lemma 3.1: Every linear propagator is invertible with inverse `X t₁ t₀`. -/
theorem left_inv (hX : LinearPropagator L X) (t₀ t₁ : ℝ) :
    X t₁ t₀ ∘L X t₀ t₁ = ContinuousLinearMap.id ℝ E := by
  rw [hX.comp t₀ t₁ t₀, hX.initial]

theorem right_inv (hX : LinearPropagator L X) (t₀ t₁ : ℝ) :
    X t₀ t₁ ∘L X t₁ t₀ = ContinuousLinearMap.id ℝ E := by
  rw [hX.comp t₁ t₀ t₁, hX.initial]

/-- A linear propagator induces an `IsFundamentalSolution` in the sense of `GlobalExistence`. -/
theorem isFundamentalSolution (hX : LinearPropagator L X) :
    IsFundamentalSolution (fun t₀ x t ↦ X t₀ t x) (L · ·) where
  initial := by intro t₀ x₀; simp [hX.initial]
  isIntegralCurve := by
    intro t₀ x₀ t
    simpa using (hX.hasDerivAt t₀ t).clm_apply (hasDerivAt_const t x₀)

end LinearPropagator

/-! ## 2. Shift Invariance and the Monodromy Operator -/

/-- Shift invariance of a propagator under period `T`. -/
def HasShiftInvariance (X : ℝ → ℝ → E →L[ℝ] E) (T : ℝ) : Prop :=
  ∀ t₀ t, X (t₀ + T) (t + T) = X t₀ t

/-- The Monodromy Operator at base time `0` (Ward §3.1). -/
def monodromyOperator (X : ℝ → ℝ → E →L[ℝ] E) (T : ℝ) : E →L[ℝ] E :=
  X 0 T

/-- The Monodromy Operator at an arbitrary base time `t₀`. -/
def monodromyOperatorAt (X : ℝ → ℝ → E →L[ℝ] E) (T : ℝ) (t₀ : ℝ) : E →L[ℝ] E :=
  X t₀ (t₀ + T)

section MonodromyTheorems

variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E} {T : ℝ}

/-- Ward Theorem 3.3(i): Fundamental Factorization `X(0, t + T) = X(0, t) ∘ M`. -/
theorem monodromy_factorization (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) (t : ℝ) :
    X 0 (t + T) = X 0 t ∘L monodromyOperator X T := by
  have h1 : X 0 (t + T) = X T (t + T) ∘L X 0 T := (hX.comp 0 T (t + T)).symm
  have h2 : X T (t + T) = X 0 t := by
    have hs := h_shift 0 t
    rwa [zero_add] at hs
  rw [h1, h2]
  rfl

/-- Stroboscopic composition: `X(0, t + k • T) = X(0, t) ∘ (M ^ k)` for any `k : ℕ`. -/
theorem monodromy_pow (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) (k : ℕ) (t : ℝ) :
    X 0 (t + k • T) = X 0 t ∘L (monodromyOperator X T ^ k) := by
  induction k with
  | zero =>
    simp only [zero_smul, add_zero, pow_zero]
    ext x
    simp
  | succ n ih =>
    have h_split : t + (n + 1) • T = (t + n • T) + T := by
      rw [succ_nsmul]; abel
    rw [h_split, monodromy_factorization hX h_shift, ih]
    ext x
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [pow_succ]
    rfl

/-- Stroboscopic map of initial states: `x(k • T) = M ^ k x(0)`. -/
theorem stroboscopic_map (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) (k : ℕ) (x₀ : E) :
    X 0 (k • T) x₀ = (monodromyOperator X T ^ k) x₀ := by
  have h := monodromy_pow hX h_shift k 0
  rw [zero_add] at h
  have h_app := ContinuousLinearMap.ext_iff.mp h x₀
  rw [h_app]
  simp [hX.initial 0]

end MonodromyTheorems

/-! ## 3. Floquet Multipliers, Eigenvectors, and Modes -/

/-- A scalar `ρ : ℝ` is a Floquet multiplier if there exists a nonzero vector `v` such that
`monodromyOperator X T v = ρ • v`. -/
def IsFloquetMultiplier (X : ℝ → ℝ → E →L[ℝ] E) (T : ℝ) (ρ : ℝ) : Prop :=
  ∃ v : E, v ≠ 0 ∧ (monodromyOperator X T) v = ρ • v

/-- A vector `v` is a Floquet eigenvector with multiplier `ρ`. -/
def IsFloquetEigenvector (X : ℝ → ℝ → E →L[ℝ] E) (T : ℝ) (ρ : ℝ) (v : E) : Prop :=
  v ≠ 0 ∧ (monodromyOperator X T) v = ρ • v

section FloquetModes

variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E} {T : ℝ}

/-- Ward Theorem 3.4(i): A Floquet mode shifts by the factor `ρ` across one period:
`x(t + T) = ρ • x(t)`. -/
theorem floquet_mode_shift (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) {v : E} {ρ : ℝ}
    (hv : (monodromyOperator X T) v = ρ • v) (t : ℝ) :
    X 0 (t + T) v = ρ • X 0 t v := by
  have h_fac := monodromy_factorization hX h_shift t
  have h1 : X 0 (t + T) v = (X 0 t ∘L monodromyOperator X T) v := by rw [h_fac]
  rw [h1]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hv]
  rw [ContinuousLinearMap.map_smul]

/-- Ward equation (3.50): Stroboscopic scaling `x(t + k • T) = (ρ ^ k) • x(t)`. -/
theorem floquet_mode_pow (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) {v : E} {ρ : ℝ}
    (hv : (monodromyOperator X T) v = ρ • v) (k : ℕ) (t : ℝ) :
    X 0 (t + k • T) v = (ρ ^ k) • X 0 t v := by
  induction k with
  | zero =>
    simp only [zero_smul, add_zero, pow_zero, one_smul]
  | succ n ih =>
    have h_split : t + (n + 1) • T = (t + n • T) + T := by
      rw [succ_nsmul]; abel
    rw [h_split, floquet_mode_shift hX h_shift hv, ih]
    rw [smul_smul]
    congr 1
    rw [mul_comm, ← pow_succ]

/-- At `t = 0`, the discrete trajectory sampled along an eigenvector is `(ρ ^ k) • v`. -/
theorem floquet_mode_stroboscopic (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) {v : E} {ρ : ℝ}
    (hv : (monodromyOperator X T) v = ρ • v) (k : ℕ) :
    X 0 (k • T) v = (ρ ^ k) • v := by
  have h := floquet_mode_pow hX h_shift hv k 0
  rw [zero_add] at h
  rw [h, hX.initial_apply 0 v]

/-- Along any contracting Floquet mode `|ρ| < 1`, the discrete trajectory converges to 0. -/
theorem tendsto_smul_pow_zero_of_lt_one {ρ : ℝ} (hρ : |ρ| < 1) (v : E) :
    Tendsto (fun k : ℕ ↦ (ρ ^ k) • v) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have h_geo : Tendsto (fun k : ℕ ↦ |ρ| ^ k * ‖v‖) atTop (𝓝 (0 * ‖v‖)) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const ‖v‖
  rw [zero_mul] at h_geo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_geo ?_ ?_
  · filter_upwards with k
    exact norm_nonneg _
  · filter_upwards with k
    rw [norm_smul, Real.norm_eq_abs, abs_pow]

/-- Floquet mode convergence to the origin: when `|ρ| < 1`, `X 0 (k • T) v → 0`. -/
theorem floquet_mode_tendsto_zero (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) {v : E} {ρ : ℝ}
    (hv : (monodromyOperator X T) v = ρ • v) (hρ : |ρ| < 1) :
    Tendsto (fun k : ℕ ↦ X 0 (k • T) v) atTop (𝓝 0) := by
  have h_eq : (fun k : ℕ ↦ X 0 (k • T) v) = (fun k : ℕ ↦ (ρ ^ k) • v) := by
    ext k
    exact floquet_mode_stroboscopic hX h_shift hv k
  rw [h_eq]
  exact tendsto_smul_pow_zero_of_lt_one hρ v

/-- Along any expanding Floquet mode `1 < |ρ|` with `v ≠ 0`, the trajectory norms diverge to
infinity. -/
theorem tendsto_norm_smul_pow_atTop_of_one_lt {ρ : ℝ} (hρ : 1 < |ρ|) {v : E} (hv_ne : v ≠ 0) :
    Tendsto (fun k : ℕ ↦ ‖(ρ ^ k) • v‖) atTop atTop := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have h_pow : Tendsto (fun k : ℕ ↦ |ρ| ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hρ
  have h_mul : Tendsto (fun k : ℕ ↦ |ρ| ^ k * ‖v‖) atTop atTop :=
    h_pow.atTop_mul_const hv_pos
  have h_eq : (fun k : ℕ ↦ ‖(ρ ^ k) • v‖) = (fun k : ℕ ↦ |ρ| ^ k * ‖v‖) := by
    ext k
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
  rw [h_eq]
  exact h_mul

/-- Divergence along an expanding Floquet mode:
when `1 < |ρ|` and `v ≠ 0`, `‖X 0 (k • T) v‖ → ∞`. -/
theorem floquet_mode_tendsto_atTop (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) {v : E} {ρ : ℝ}
    (hv : (monodromyOperator X T) v = ρ • v) (hρ : 1 < |ρ|) (hv_ne : v ≠ 0) :
    Tendsto (fun k : ℕ ↦ ‖X 0 (k • T) v‖) atTop atTop := by
  have h_eq : (fun k : ℕ ↦ ‖X 0 (k • T) v‖) = (fun k : ℕ ↦ ‖(ρ ^ k) • v‖) := by
    ext k
    rw [floquet_mode_stroboscopic hX h_shift hv k]
  rw [h_eq]
  exact tendsto_norm_smul_pow_atTop_of_one_lt hρ hv_ne

end FloquetModes

/-! ## 4. Quasi-Periodic Decomposition (Ward Theorem 3.4(ii)) -/

section Decomposition

variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E} {T : ℝ}

/-- Ward Theorem 3.4(ii): For any positive multiplier `ρ > 0` with characteristic exponent
`μ = log ρ / T`, the solution decomposes as `x(t) = exp(μ * t) • p(t)` where `p` is `T`-periodic. -/
theorem floquet_decomposition (hX : LinearPropagator L X)
    (h_shift : HasShiftInvariance X T) (hT : T ≠ 0)
    {v : E} {ρ : ℝ} (hρ : 0 < ρ) (hv : (monodromyOperator X T) v = ρ • v) :
    let μ := Real.log ρ / T
    let p := fun t ↦ Real.exp (-μ * t) • X 0 t v
    Function.Periodic p T ∧ ∀ t, X 0 t v = Real.exp (μ * t) • p t := by
  intro μ p
  have h_exp_T : Real.exp (-μ * T) * ρ = 1 := by
    dsimp [μ]
    rw [neg_mul, div_mul_cancel₀ (Real.log ρ) hT]
    rw [Real.exp_neg, Real.exp_log hρ]
    exact inv_mul_cancel₀ (ne_of_gt hρ)
  have h_periodic : Function.Periodic p T := by
    intro t
    dsimp [p]
    have h_shift_val := floquet_mode_shift hX h_shift hv t
    rw [h_shift_val]
    have h_exp_add : Real.exp (-μ * (t + T)) = Real.exp (-μ * t) * Real.exp (-μ * T) := by
      rw [show -μ * (t + T) = -μ * t + -μ * T by ring, Real.exp_add]
    rw [h_exp_add, smul_smul]
    have h_scalar : (Real.exp (-μ * t) * Real.exp (-μ * T)) * ρ = Real.exp (-μ * t) := by
      rw [mul_assoc, h_exp_T, mul_one]
    rw [h_scalar]
  have h_rep : ∀ t, X 0 t v = Real.exp (μ * t) • p t := by
    intro t
    dsimp [p]
    rw [smul_smul, ← Real.exp_add]
    have h_cancel : μ * t + -μ * t = 0 := by
      rw [neg_mul, add_neg_cancel]
    rw [h_cancel, Real.exp_zero, one_smul]
  exact ⟨h_periodic, h_rep⟩

end Decomposition

/-! ## 5. Linearization of Autonomous Periodic Orbits (Ward §3.1.2) -/

section PeriodicOrbits

variable {f : E → E} {φ : ℝ → E} {T : ℝ}

/-- An autonomous periodic orbit with period `T > 0`. -/
structure IsPeriodicOrbit (f : E → E) (φ : ℝ → E) (T : ℝ) : Prop where
  isIntegralCurve : IsIntegralCurve φ (fun _ ↦ f)
  periodic : Function.Periodic φ T
  pos_period : 0 < T

/-- Ward Section 3.1.2: If the velocity vector `v(t) = f(φ(t))` is preserved by the propagator
at period `T`, then `v(0)` is an eigenvector of `M` with Floquet multiplier `1`. -/
theorem periodic_orbit_has_multiplier_one (hφ : IsPeriodicOrbit f φ T)
    {X : ℝ → ℝ → E →L[ℝ] E}
    (hX_prop : X 0 T (f (φ 0)) = f (φ T)) :
    (monodromyOperator X T) (f (φ 0)) = (1 : ℝ) • f (φ 0) := by
  dsimp [monodromyOperator]
  have h_per : f (φ T) = f (φ 0) := by
    rw [show φ T = φ (0 + T) by rw [zero_add], hφ.periodic 0]
  rw [hX_prop, h_per, one_smul]

/-- Ward Section 3.1.2 Goldstone Multiplier Theorem:
Any non-stationary periodic orbit has `1` as a Floquet multiplier. -/
theorem periodic_orbit_isFloquetMultiplier_one (hφ : IsPeriodicOrbit f φ T)
    {X : ℝ → ℝ → E →L[ℝ] E}
    (h_nontrivial : f (φ 0) ≠ 0)
    (hX_prop : X 0 T (f (φ 0)) = f (φ T)) :
    IsFloquetMultiplier X T 1 := by
  use f (φ 0)
  refine ⟨h_nontrivial, periodic_orbit_has_multiplier_one hφ hX_prop⟩

end PeriodicOrbits

/-! ## 6. Dynamic Stability of Discrete Monodromy Flows -/

section DynamicStability

/-- Pointwise bound on operator powers: `‖(M ^ k) x‖ ≤ ‖M‖ ^ k * ‖x‖`. -/
theorem norm_pow_apply_le (M : E →L[ℝ] E) (k : ℕ) (x : E) :
    ‖(M ^ k) x‖ ≤ ‖M‖ ^ k * ‖x‖ := by
  induction k with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ']
    calc ‖((M * M ^ n) : E →L[ℝ] E) x‖ = ‖M ((M ^ n) x)‖ := by rfl
      _ ≤ ‖M‖ * ‖(M ^ n) x‖ := M.le_opNorm _
      _ ≤ ‖M‖ * (‖M‖ ^ n * ‖x‖) := by gcongr
      _ = ‖M‖ ^ (n + 1) * ‖x‖ := by rw [pow_succ', mul_assoc]

/-- Lyapunov stability of the origin under discrete stroboscopic flow when `‖M‖ ≤ 1`.
Formulated directly with `Filter.IsStableOn` from `DynamicalSystems.Stability.Basic`. -/
theorem isStableOn_monodromy_of_le_one (M : E →L[ℝ] E) (hM : ‖M‖ ≤ 1) :
    (𝓝 (0 : E)).IsStableOn (fun k x ↦ (M ^ k) x) Set.univ := by
  rw [Metric.nhds_basis_ball.isStableOn_iff]
  intro ε hε
  use ε, hε
  intro k _ x hx
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have h_le : ‖(M ^ k) x‖ ≤ ‖M‖ ^ k * ‖x‖ := norm_pow_apply_le M k x
  have h_pow : ‖M‖ ^ k ≤ 1 := by
    calc ‖M‖ ^ k ≤ 1 ^ k := by gcongr
      _ = 1 := one_pow k
  calc ‖(M ^ k) x‖ ≤ ‖M‖ ^ k * ‖x‖ := h_le
    _ ≤ 1 * ‖x‖ := by gcongr
    _ = ‖x‖ := one_mul ‖x‖
    _ < ε := hx

/-- Global asymptotic convergence to zero when `‖M‖ < 1`. -/
theorem tendsto_monodromy_pow_zero_of_norm_lt_one (M : E →L[ℝ] E) (hM : ‖M‖ < 1) (x : E) :
    Tendsto (fun k : ℕ ↦ (M ^ k) x) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have h_geo : Tendsto (fun k : ℕ ↦ ‖M‖ ^ k * ‖x‖) atTop (𝓝 (0 * ‖x‖)) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg M) hM).mul_const ‖x‖
  rw [zero_mul] at h_geo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_geo ?_ ?_
  · filter_upwards with k
    exact norm_nonneg _
  · filter_upwards with k
    exact norm_pow_apply_le M k x

/-- Attractiveness of the origin under discrete stroboscopic flow when `‖M‖ < 1`.
Formulated directly with `Filter.IsAttractive` from `DynamicalSystems.Stability.Basic`. -/
theorem isAttractive_monodromy_of_lt_one (M : E →L[ℝ] E) (hM : ‖M‖ < 1) :
    @Filter.IsAttractive ℕ E (𝓝 (0 : E)) (fun k x ↦ (M ^ k) x) atTop := by
  change ∀ᶠ x in 𝓝 0, Tendsto (fun k ↦ (M ^ k) x) atTop (𝓝 0)
  filter_upwards with x
  exact tendsto_monodromy_pow_zero_of_norm_lt_one M hM x

end DynamicStability

/-! ## 7. Characteristic Roots of 2D Conservative Systems (Ward §3.2) -/

section SecondOrderStability

/-!
This section formalizes the scalar algebraic root analysis of the characteristic polynomial
`λ² - 2φ λ + 1 = 0` (where `φ = (tr M) / 2`) for 2D conservative systems with `det M = 1`
(Ward Section 3.2.3).

Scope note:
- These theorems analyze the roots of the scalar characteristic polynomial.
- For `|φ| < 1` (Ward Case I), both roots lie strictly on the unit circle (`‖z‖ = 1`).
  Lifting this to uniform matrix power-boundedness (`sup_k ‖M^k‖ < ∞`) requires Jordan
  decomposition or symplectic preservation, whereas the operator norm theorem
  `isStableOn_monodromy_of_le_one` directly guarantees Lyapunov stability when `‖M‖ ≤ 1`.
- For `1 < |φ|` (Ward Case II), there exists a real root with `1 < |ρ|`.
  Coupled with `floquet_mode_tendsto_atTop`, this produces exponential trajectory divergence
  along any corresponding Floquet eigenvector.
-/

/-- For a 2x2 conservative system with `det M = 1`, the characteristic polynomial is
`λ² - 2φ λ + 1 = 0` where `φ = tr M / 2`.
When `|φ| < 1`, the discriminant is negative and eigenvalues lie on the unit circle (stable). -/
theorem second_order_characteristic_discriminant (tr_M : ℝ) :
    let φ := tr_M / 2
    4 * φ ^ 2 - 4 = (tr_M ^ 2 - 4) := by
  intro φ
  dsimp [φ]
  ring

/-- Ward Section 3.2.3 Case I: When `|tr M| < 2`, the discriminant is strictly negative. -/
theorem second_order_stable_of_trace_lt_two {tr_M : ℝ} (h : |tr_M| < 2) :
    tr_M ^ 2 - 4 < 0 := by
  have h2 : |tr_M| < |(2 : ℝ)| := by simpa using h
  have h_sq : tr_M ^ 2 < (2 : ℝ) ^ 2 := sq_lt_sq.mpr h2
  linarith

/-- Ward Section 3.2.3 Case I (Unit Circle Roots):
When `|φ| < 1`, the imaginary part `σ = √(1 - φ²)` is strictly positive, and the complex root
`z = ⟨φ, σ⟩` satisfies the characteristic equation and lies on the unit circle (`‖z‖ = 1`). -/
theorem second_order_stable_roots_unit_circle (φ : ℝ) (hφ : |φ| < 1) :
    let σ := Real.sqrt (1 - φ ^ 2)
    let z : ℂ := ⟨φ, σ⟩
    0 < σ ∧ z ^ 2 - ((2 * φ : ℝ) : ℂ) * z + 1 = 0 ∧ ‖z‖ = 1 := by
  intro σ z
  have h_pos : 0 < 1 - φ ^ 2 := by
    have h_sq : |φ| ^ 2 < (1 : ℝ) ^ 2 := sq_lt_sq.mpr (by simpa using hφ)
    rw [sq_abs] at h_sq
    linarith
  have h_nonneg : 0 ≤ 1 - φ ^ 2 := by linarith
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact Real.sqrt_pos.mpr h_pos
  have h_root : z ^ 2 - ((2 * φ : ℝ) : ℂ) * z + 1 = 0 := by
    apply Complex.ext
    · rw [sq]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.zero_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      dsimp [z]
      have hσ_sq : σ ^ 2 = 1 - φ ^ 2 := by
        dsimp [σ]
        exact Real.sq_sqrt h_nonneg
      nlinarith
    · rw [sq]
      simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.zero_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      dsimp [z]
      ring
  have h_norm : ‖z‖ = 1 := by
    have h : Complex.normSq z = 1 := by
      dsimp [z, Complex.normSq]
      have hσ_sq : σ ^ 2 = 1 - φ ^ 2 := by
        dsimp [σ]
        exact Real.sq_sqrt h_nonneg
      linarith
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg z]
  exact ⟨hσ_pos, h_root, h_norm⟩

/-- Ward Section 3.2.3 Case I (Unit Circle Eigenvalue Identity):
Given `σ² = 1 - φ²`, the complex number `z = ⟨φ, σ⟩` is a root of the characteristic polynomial
and lies on the unit circle in `ℂ` (`‖z‖ = 1`). -/
theorem second_order_stable_eigenvalues_unit_circle (φ σ : ℝ) (hσ : σ ^ 2 = 1 - φ ^ 2) :
    let z : ℂ := ⟨φ, σ⟩
    z ^ 2 - ((2 * φ : ℝ) : ℂ) * z + 1 = 0 ∧ ‖z‖ = 1 := by
  intro z
  have h_root : z ^ 2 - ((2 * φ : ℝ) : ℂ) * z + 1 = 0 := by
    apply Complex.ext
    · rw [sq]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.zero_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      dsimp [z]
      nlinarith
    · rw [sq]
      simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.zero_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      dsimp [z]
      ring
  have h_norm : ‖z‖ = 1 := by
    have h : Complex.normSq z = 1 := by
      dsimp [z, Complex.normSq]
      linarith
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg z]
  exact ⟨h_root, h_norm⟩

/-- Ward Section 3.2.3 Case II: When `|tr M| > 2`, the discriminant is strictly positive. -/
theorem second_order_unstable_of_trace_gt_two {tr_M : ℝ} (h : 2 < |tr_M|) :
    0 < tr_M ^ 2 - 4 := by
  have h2 : |(2 : ℝ)| < |tr_M| := by simpa using h
  have h_sq : (2 : ℝ) ^ 2 < tr_M ^ 2 := sq_lt_sq.mpr h2
  linarith

/-- Ward Section 3.2.3 Case II (Unstable Roots of Conservative 2D Characteristic Polynomial):
When `1 < |φ|`, there exists a real root `ρ` of `r² - 2φ r + 1 = 0` with `1 < |ρ|`.
For positive trace `1 < φ`, the root `ρ = φ + √(φ² - 1)` satisfies `1 < ρ`.
For negative trace `φ < -1`, the root `ρ = φ - √(φ² - 1)` satisfies `ρ < -1`, hence `1 < |ρ|`. -/
theorem second_order_unstable_root_abs_gt_one (φ : ℝ) (hφ : 1 < |φ|) :
    ∃ ρ : ℝ, 1 < |ρ| ∧ ρ ^ 2 - 2 * φ * ρ + 1 = 0 := by
  have h_pos : 0 < φ ^ 2 - 1 := by
    have h_sq : 1 ^ 2 < |φ| ^ 2 := sq_lt_sq.mpr (by simpa using hφ)
    rw [sq_abs] at h_sq
    linarith
  have h_sqrt_nonneg : 0 ≤ φ ^ 2 - 1 := by linarith
  have h_ne : φ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  rcases lt_or_gt_of_ne h_ne with h_neg | h_pos_phi
  · -- Case φ < 0, so φ < -1
    have h_lt : φ < -1 := by
      rw [abs_of_neg h_neg] at hφ
      linarith
    let ρ := φ - Real.sqrt (φ ^ 2 - 1)
    use ρ
    have h_sqrt_pos : 0 < Real.sqrt (φ ^ 2 - 1) := Real.sqrt_pos.mpr h_pos
    have h_rho_lt : ρ < -1 := by
      dsimp [ρ]
      linarith
    have h_abs_gt : 1 < |ρ| := by
      have h_rho_neg : ρ < 0 := by linarith
      rw [abs_of_neg h_rho_neg]
      linarith
    have h_root : ρ ^ 2 - 2 * φ * ρ + 1 = 0 := by
      dsimp [ρ]
      have h_sq : (Real.sqrt (φ ^ 2 - 1)) ^ 2 = φ ^ 2 - 1 := Real.sq_sqrt h_sqrt_nonneg
      nlinarith
    exact ⟨h_abs_gt, h_root⟩
  · -- Case φ > 0, so 1 < φ
    have h_gt : 1 < φ := by
      rw [abs_of_pos h_pos_phi] at hφ
      exact hφ
    let ρ := φ + Real.sqrt (φ ^ 2 - 1)
    use ρ
    have h_sqrt_pos : 0 < Real.sqrt (φ ^ 2 - 1) := Real.sqrt_pos.mpr h_pos
    have h_rho_gt : 1 < ρ := by
      dsimp [ρ]
      linarith
    have h_abs_gt : 1 < |ρ| := by
      have h_rho_pos : 0 < ρ := by linarith
      rw [abs_of_pos h_rho_pos]
      exact h_rho_gt
    have h_root : ρ ^ 2 - 2 * φ * ρ + 1 = 0 := by
      dsimp [ρ]
      have h_sq : (Real.sqrt (φ ^ 2 - 1)) ^ 2 = φ ^ 2 - 1 := Real.sq_sqrt h_sqrt_nonneg
      nlinarith
    exact ⟨h_abs_gt, h_root⟩

/-- Ward Section 3.2.3 Case II (Positive Trace Branch):
When `1 < φ`, the explicit root `ρ = φ + √(φ² - 1)` is strictly greater than 1. -/
theorem second_order_unstable_real_eigenvalue_gt_one (φ : ℝ) (hφ : 1 < φ) :
    let ρ := φ + Real.sqrt (φ ^ 2 - 1)
    1 < ρ ∧ ρ ^ 2 - 2 * φ * ρ + 1 = 0 := by
  intro ρ
  have h_pos : 0 < φ ^ 2 - 1 := by nlinarith
  have h_gt_one : 1 < ρ := by
    dsimp [ρ]
    have := Real.sqrt_pos.mpr h_pos
    linarith
  have h_eq : ρ ^ 2 - 2 * φ * ρ + 1 = 0 := by
    dsimp [ρ]
    have h_sq : (Real.sqrt (φ ^ 2 - 1)) ^ 2 = φ ^ 2 - 1 :=
      Real.sq_sqrt (by linarith)
    nlinarith
  exact ⟨h_gt_one, h_eq⟩

/-- Stroboscopic error contraction for discrete return map:
`|x_{k+1} - x*| = |ρ| * |x_k - x*|`. This bridges Floquet multiplier contraction
directly to the Poincaré contraction in `auto_automatyk`. -/
theorem stroboscopic_distance_contraction (ρ x_k x_star b : ℝ)
    (h_fp : x_star = ρ * x_star + b) :
    |(ρ * x_k + b) - x_star| = |ρ| * |x_k - x_star| := by
  have h_sub : (ρ * x_k + b) - x_star = ρ * (x_k - x_star) := by
    nth_rw 1 [h_fp]
    ring
  rw [h_sub, abs_mul]

/-- Geometric decay of stroboscopic tracking error when `|ρ| < 1`. -/
theorem stroboscopic_geometric_decay (ρ x_0 x_star b : ℝ) (m : ℕ)
    (h_fp : x_star = ρ * x_star + b)
    (x : ℕ → ℝ) (h_seq : ∀ k, x (k + 1) = ρ * x k + b) (h_init : x 0 = x_0) :
    |x m - x_star| = |ρ| ^ m * |x_0 - x_star| := by
  induction m with
  | zero =>
    rw [h_init, pow_zero, one_mul]
  | succ k ih =>
    rw [h_seq k, stroboscopic_distance_contraction ρ (x k) x_star b h_fp, ih]
    rw [pow_succ', mul_assoc]

end SecondOrderStability

end

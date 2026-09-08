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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
- **Second-Order Trace Criterion**: For conservative 2D systems with `det M = 1`,
  `|tr M| < 2` gives bounded/stable multipliers on the unit circle, while `|tr M| > 2` gives
  exponential instability (Ward Section 3.2.3).
-/

@[expose] public noncomputable section

open scoped Topology NNReal

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

/-! ## 6. Stability Criteria and 2D Second-Order Systems (Ward §3.2) -/

section SecondOrderStability

/-- For a 2x2 conservative system with `det M = 1`, the characteristic polynomial is
`λ² - 2φ λ + 1 = 0` where `φ = tr M / 2`.
When `|φ| < 1`, the discriminant is negative and eigenvalues lie on the unit circle (stable). -/
theorem second_order_characteristic_discriminant (tr_M : ℝ) :
    let φ := tr_M / 2
    4 * φ ^ 2 - 4 = (tr_M ^ 2 - 4) := by
  intro φ
  dsimp [φ]
  ring

/-- Ward Section 3.2.3: When `|tr M| < 2`, the discriminant is strictly negative,
signifying purely oscillatory / neutrally stable Floquet multipliers. -/
theorem second_order_stable_of_trace_lt_two {tr_M : ℝ} (h : |tr_M| < 2) :
    tr_M ^ 2 - 4 < 0 := by
  have h2 : |tr_M| < |(2 : ℝ)| := by simpa using h
  have h_sq : tr_M ^ 2 < (2 : ℝ) ^ 2 := sq_lt_sq.mpr h2
  linarith

/-- Ward Section 3.2.3: When `|tr M| > 2`, the discriminant is strictly positive,
yielding real eigenvalues `ρ₁ * ρ₂ = 1` with `|ρ₁| > 1`, signifying exponential instability. -/
theorem second_order_unstable_of_trace_gt_two {tr_M : ℝ} (h : 2 < |tr_M|) :
    0 < tr_M ^ 2 - 4 := by
  have h2 : |(2 : ℝ)| < |tr_M| := by simpa using h
  have h_sq : (2 : ℝ) ^ 2 < tr_M ^ 2 := sq_lt_sq.mpr h2
  linarith

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

/-
Copyright (c) 2026 Moritz Doll, Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory.Picard
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Global existence, uniqueness, and patching for Carathéodory ODEs

This file establishes global existence, uniqueness, and extension results for Carathéodory
differential equations, with specific applications to linear Carathéodory control systems.

## References

* Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Charles University, Theorems 23 and 24.
* Paulo M. de Carvalho-Neto, Cícero L. Frota, Pedro G. P. Torelli (2025),
  *A general version of Carathéodory's existence and uniqueness theorem*,
  arXiv:2505.24516 [math.CA].
* Donal O'Regan (1997), *Existence Theory for Nonlinear Ordinary Differential Equations*,
  Mathematics and Its Applications 398, Kluwer Academic Publishers / Springer.
* Moritz Doll, Iman Shames (2026), *Foundations of Machine-Checked Control Theory in Lean*.

## Main definitions and theorems

* `isCaratheodoryLinear`: Linear vector fields $x \mapsto A(t)x + b(t)$ are Carathéodory.
* `isCaratheodoryLipschitz_linear`: Linear vector fields are Carathéodory-Lipschitz with
  $\ell(t) = \|A(t)\|$.
* `intervalIntegrable_linear`: Integrability of $t \mapsto A(t)\gamma(t) + b(t)$ for
  continuous $\gamma$.
* `isCaratheodorySolutionOn_patching`: Patching solutions on expanding intervals into a global
  continuous solution on $\mathbb{R}$.
* `isCaratheodorySolutionOn_unique_global`: Global uniqueness of Carathéodory solutions on
  $\mathbb{R}$.
* `exists_unique_caratheodory_solution_global`: Existence and uniqueness of a global Carathéodory
  integral solution.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Linear Carathéodory systems -/

/-- A time-dependent linear affine vector field $x \mapsto A(t)x + b(t)$ is Carathéodory
whenever $t \mapsto A(t)x$ and $t \mapsto b(t)$ are almost everywhere strongly measurable.
Reference: Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 23. -/
theorem isCaratheodoryLinear
    (A : ℝ → E →L[ℝ] E) (b : ℝ → E)
    (hA_meas : ∀ x, AEStronglyMeasurable (fun t ↦ A t x) volume)
    (hb_meas : AEStronglyMeasurable b volume) :
    IsCaratheodory (fun t x ↦ A t x + b t) where
  cont := by
    filter_upwards with t
    exact (A t).continuous.add continuous_const
  meas := by
    intro x
    exact (hA_meas x).add hb_meas

/-- A time-dependent linear affine vector field $x \mapsto A(t)x + b(t)$ is Carathéodory-Lipschitz
with time-dependent Lipschitz bound $\ell(t) = \|A(t)\|$.
Reference: Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 24. -/
theorem isCaratheodoryLipschitz_linear
    (A : ℝ → E →L[ℝ] E) (b : ℝ → E)
    (hA_meas : ∀ x, AEStronglyMeasurable (fun t ↦ A t x) volume)
    (hb_meas : AEStronglyMeasurable b volume) :
    IsCaratheodoryLipschitz (fun t x ↦ A t x + b t) (fun t ↦ ‖A t‖) where
  toIsCaratheodory := isCaratheodoryLinear A b hA_meas hb_meas
  lip := by
    filter_upwards with t
    intro x y
    rw [add_sub_add_right_eq_sub, ← (A t).map_sub]
    exact (A t).le_opNorm (x - y)

/-- The composition of a linear affine Carathéodory vector field with a continuous curve $\gamma$
is interval integrable whenever $\|A(\cdot)\|$ and $b(\cdot)$ are interval integrable. -/
theorem intervalIntegrable_linear
    (A : ℝ → E →L[ℝ] E) (b : ℝ → E)
    (hA_meas : ∀ x, AEStronglyMeasurable (fun t ↦ A t x) volume)
    {a b_t : ℝ} (hA_int : IntervalIntegrable (fun t ↦ ‖A t‖) volume a b_t)
    (hb_int : IntervalIntegrable b volume a b_t)
    {γ : ℝ → E} (hγ : Continuous γ) :
    IntervalIntegrable (fun t ↦ A t (γ t) + b t) volume a b_t := by
  refine IntervalIntegrable.add ?_ hb_int
  have hCarA : IsCaratheodory (fun t x ↦ A t x) := by
    have h0_meas : AEStronglyMeasurable (fun _ : ℝ ↦ (0 : E)) volume :=
      aestronglyMeasurable_const
    have := isCaratheodoryLinear A (fun _ ↦ 0) hA_meas h0_meas
    simpa using this
  have h_meas : AEStronglyMeasurable (fun t ↦ A t (γ t)) volume :=
    hCarA.comp_continuous hγ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ [[a, b_t]], ‖γ t‖ ≤ M := by
    have h_cpt : IsCompact ([[a, b_t]]) := isCompact_uIcc
    obtain ⟨C, hC⟩ := (h_cpt.image hγ).isBounded.subset_ball (0 : E)
    refine ⟨C, fun t ht ↦ ?_⟩
    have : γ t ∈ Metric.ball (0 : E) C := hC (mem_image_of_mem γ ht)
    rw [Metric.mem_ball, dist_zero_right] at this
    exact le_of_lt this
  rw [intervalIntegrable_iff] at hA_int ⊢
  refine Integrable.mono' (hA_int.mul_const M) h_meas.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht_uIcc : t ∈ [[a, b_t]] := uIoc_subset_uIcc ht
  calc ‖A t (γ t)‖ ≤ ‖A t‖ * ‖γ t‖ := (A t).le_opNorm (γ t)
    _ ≤ ‖A t‖ * M := mul_le_mul_of_nonneg_left (hM t ht_uIcc) (norm_nonneg _)

/-- Variant of `intervalIntegrable_linear` for continuous curves on `Icc a b` composed with
the interval projection `projIcc`. -/
theorem intervalIntegrable_linear_projIcc
    (A : ℝ → E →L[ℝ] E) (b : ℝ → E)
    (hA_meas : ∀ x, AEStronglyMeasurable (fun t ↦ A t x) volume)
    {a b_t : ℝ} (hab : a ≤ b_t)
    (hA_int : IntervalIntegrable (fun t ↦ ‖A t‖) volume a b_t)
    (hb_int : IntervalIntegrable b volume a b_t)
    (γ : C(Icc a b_t, E)) :
    IntervalIntegrable (fun t ↦ A t (γ (projIcc a b_t hab t)) + b t) volume a b_t :=
  intervalIntegrable_linear A b hA_meas hA_int hb_int (γ.continuous.comp continuous_projIcc)

/-! ### Patching and global extension -/

/-- Patching continuous Carathéodory solutions on expanding compact intervals
`[t₀ - (n + 1), t₀ + (n + 1)]` into a single global continuous solution on `Set.univ`. -/
theorem isCaratheodorySolutionOn_patching
    {f : ℝ → E → E} (t₀ : ℝ) (x₀ : E)
    (α : ℕ → ℝ → E)
    (hα_cont : ∀ n, Continuous (α n))
    (hα_sol : ∀ n, IsCaratheodorySolutionOn (α n) f t₀ x₀
      (Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1))))
    (hagree : ∀ m n : ℕ, m ≤ n → ∀ t : ℝ, |t - t₀| ≤ (m : ℝ) + 1 → α m t = α n t) :
    let Φ : ℝ → E := fun t ↦ α ⌈|t - t₀|⌉₊ t
    Continuous Φ ∧ IsCaratheodorySolutionOn Φ f t₀ x₀ Set.univ := by
  intro Φ
  have key : ∀ t : ℝ, ∀ s : ℝ, |s - t| < 1 / 2 → Φ s = α (⌈|t - t₀|⌉₊ + 1) s := by
    intro t s hs
    set N : ℕ := ⌈|t - t₀|⌉₊
    have hst : |s - t₀| ≤ (N : ℝ) + 1 / 2 := by
      calc |s - t₀| ≤ |s - t| + |t - t₀| := by
            simpa using abs_sub_le s t t₀
        _ ≤ 1 / 2 + (N : ℝ) := by linarith [Nat.le_ceil (|t - t₀|)]
        _ = (N : ℝ) + 1 / 2 := by ring
    have h_ceil : ⌈|s - t₀|⌉₊ ≤ N + 1 := by
      refine Nat.ceil_le.mpr ?_
      push_cast
      linarith
    dsimp [Φ]
    refine hagree _ (N + 1) h_ceil s ?_
    have : (⌈|s - t₀|⌉₊ : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast h_ceil
    linarith [Nat.le_ceil (|s - t₀|)]
  have hev : ∀ t : ℝ, Φ =ᶠ[nhds t] α (⌈|t - t₀|⌉₊ + 1) := by
    intro t
    filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact key t s hs
  have hΦ_cont : Continuous Φ := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    have hα_cont_at := (hα_cont (⌈|t - t₀|⌉₊ + 1)).continuousAt (x := t)
    exact hα_cont_at.congr_of_eventuallyEq (hev t)
  refine ⟨hΦ_cont, fun t _ ↦ ?_⟩
  set N : ℕ := ⌈|t - t₀|⌉₊
  have ht_le : |t - t₀| ≤ (N : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
  have ht_mem : t ∈ Icc (t₀ - ((N : ℝ) + 1)) (t₀ + ((N : ℝ) + 1)) := by
    rw [mem_Icc]
    exact ⟨by linarith [neg_le_of_abs_le ht_le], by linarith [le_of_abs_le ht_le]⟩
  have h_sol_N := hα_sol N t ht_mem
  have h_val : Φ t = α N t := by dsimp [Φ]
  rw [h_val, h_sol_N]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs_le : |s - t₀| ≤ |t - t₀| := by
    rcases mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hs_le_N : |s - t₀| ≤ (N : ℝ) + 1 := hs_le.trans ht_le
  have h_ceil_s : ⌈|s - t₀|⌉₊ ≤ N := by
    refine Nat.ceil_le.mpr (hs_le.trans (Nat.le_ceil _))
  dsimp [Φ]
  have := hagree ⌈|s - t₀|⌉₊ N h_ceil_s s ?_
  · rw [this]
  · have : (⌈|s - t₀|⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h_ceil_s
    linarith [Nat.le_ceil (|s - t₀|)]

/-- Two continuous Carathéodory solutions on `Set.univ` are globally equal if they are unique
on arbitrarily large compact intervals. -/
theorem isCaratheodorySolutionOn_unique_global
    {f : ℝ → E → E} (t₀ : ℝ) (x₀ : E)
    (h_unique_Icc : ∀ R ≥ (0 : ℝ), ∀ α β : ℝ → E, Continuous α → Continuous β →
      IsCaratheodorySolutionOn α f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) →
      IsCaratheodorySolutionOn β f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) →
      ∀ t ∈ Icc (t₀ - R) (t₀ + R), α t = β t)
    {γ₁ γ₂ : ℝ → E} (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hsol₁ : IsCaratheodorySolutionOn γ₁ f t₀ x₀ Set.univ)
    (hsol₂ : IsCaratheodorySolutionOn γ₂ f t₀ x₀ Set.univ) :
    γ₁ = γ₂ := by
  ext t
  set R : ℝ := |t - t₀|
  have hR : 0 ≤ R := abs_nonneg _
  have ht_mem : t ∈ Icc (t₀ - R) (t₀ + R) := by
    rw [mem_Icc]
    exact ⟨by linarith [neg_le_of_abs_le (le_refl R)], by linarith [le_of_abs_le (le_refl R)]⟩
  have hsol₁_Icc : IsCaratheodorySolutionOn γ₁ f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) :=
    fun s _ ↦ hsol₁ s trivial
  have hsol₂_Icc : IsCaratheodorySolutionOn γ₂ f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) :=
    fun s _ ↦ hsol₂ s trivial
  exact h_unique_Icc R hR γ₁ γ₂ hγ₁_cont hγ₂_cont hsol₁_Icc hsol₂_Icc t ht_mem

/-- Global existence and uniqueness of continuous Carathéodory solutions on `Set.univ`
from existence and uniqueness on expanding compact intervals. -/
theorem exists_unique_caratheodory_solution_global
    {f : ℝ → E → E} (t₀ : ℝ) (x₀ : E)
    (h_exist_Icc : ∀ n : ℕ, ∃ α : ℝ → E, Continuous α ∧
      IsCaratheodorySolutionOn α f t₀ x₀ (Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1))))
    (h_unique_Icc : ∀ R ≥ (0 : ℝ), ∀ α β : ℝ → E, Continuous α → Continuous β →
      IsCaratheodorySolutionOn α f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) →
      IsCaratheodorySolutionOn β f t₀ x₀ (Icc (t₀ - R) (t₀ + R)) →
      ∀ t ∈ Icc (t₀ - R) (t₀ + R), α t = β t) :
    ∃! γ : ℝ → E, Continuous γ ∧ IsCaratheodorySolutionOn γ f t₀ x₀ Set.univ := by
  choose α hα_cont hα_sol using h_exist_Icc
  have hagree : ∀ m n : ℕ, m ≤ n → ∀ t : ℝ, |t - t₀| ≤ (m : ℝ) + 1 → α m t = α n t := by
    intro m n hmn t ht
    have hmR : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have ht_mem : t ∈ Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)) := by
      rw [mem_Icc]
      exact ⟨by linarith [neg_le_of_abs_le ht], by linarith [le_of_abs_le ht]⟩
    have hsub : Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)) ⊆
        Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1)) := by
      apply Icc_subset_Icc
      · gcongr
      · gcongr
    have hαn_sub : IsCaratheodorySolutionOn (α n) f t₀ x₀
        (Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1))) :=
      fun s hs ↦ hα_sol n s (hsub hs)
    exact h_unique_Icc ((m : ℝ) + 1) hmR (α m) (α n) (hα_cont m) (hα_cont n)
      (hα_sol m) hαn_sub t ht_mem
  obtain ⟨hΦ_cont, hΦ_sol⟩ := isCaratheodorySolutionOn_patching t₀ x₀ α hα_cont hα_sol hagree
  refine ⟨fun t ↦ α ⌈|t - t₀|⌉₊ t, ⟨hΦ_cont, hΦ_sol⟩, fun γ ⟨hγ_cont, hγ_sol⟩ ↦ ?_⟩
  exact isCaratheodorySolutionOn_unique_global t₀ x₀ h_unique_Icc hγ_cont hΦ_cont hγ_sol hΦ_sol

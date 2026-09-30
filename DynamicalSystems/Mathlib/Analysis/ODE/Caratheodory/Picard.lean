/-
Copyright (c) 2026 Moritz Doll, Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Order.Compact

/-! # Picard operator and local existence-uniqueness for Carathéodory ODEs

This file develops the Generalized Picard-Lindelöf contraction mapping principle
for Carathéodory differential equations on compact intervals where the $L^1$ bound
satisfies $\int_a^b \ell(s) ds < 1$.

## References

* Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Charles University, Theorem 8.
* Paulo M. de Carvalho-Neto, Cícero L. Frota, Pedro G. P. Torelli (2025),
  *A general version of Carathéodory's existence and uniqueness theorem*,
  arXiv:2505.24516 [math.CA], Theorems 2 and 14.
* Donal O'Regan (1997), *Existence Theory for Nonlinear Ordinary Differential Equations*,
  Mathematics and Its Applications 398, Kluwer Academic Publishers / Springer, Theorem 3.4.

## Main definitions

* `caratheodoryPicardCM`: The Picard iteration operator as a continuous self-map on
  `C(Icc a b, E)`.

## Main theorems

* `dist_caratheodoryPicardCM_le`: Contraction estimate with Lipschitz constant
  $\int_a^b \ell(s) ds$.
* `exists_unique_caratheodory_solution_of_small_integral`: Existence and uniqueness of
  Carathéodory solutions on compact intervals with $\int_a^b \ell(s) ds < 1$.
* `isCaratheodorySolutionOn_unique_of_small_integral`: Uniqueness of any two Carathéodory
  solutions on compact intervals with $\int_a^b \ell(s) ds < 1$.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Function
open scoped Interval NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le_of_mul_le_mul_right_zero {M c : ℝ} (hM : 0 ≤ M) (hc : c < 1) (hle : M ≤ c * M) :
    M = 0 := by
  have : (1 - c) * M ≤ 0 := by linarith
  have hpos : 0 < 1 - c := by linarith
  have hMle : M ≤ 0 := nonpos_of_mul_nonpos_right this hpos
  exact le_antisymm hMle hM

theorem uIoc_subset_uIoc_of_mem_Icc {a b t₀ t : ℝ} (hab : a ≤ b)
    (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) :
    Ι t₀ t ⊆ Ι a b := by
  rw [uIoc, uIoc, min_eq_left hab, max_eq_right hab]
  apply Ioc_subset_Ioc
  · exact le_min ht₀.1 ht.1
  · exact max_le ht₀.2 ht.2

theorem uIoc_subset_Icc_of_mem_Icc {a b t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) :
    Ι t₀ t ⊆ Icc a b := by
  refine subset_trans uIoc_subset_uIcc ?_
  exact uIcc_subset_Icc ht₀ ht

/-- The Picard operator on continuous curves `C(Icc a b, E)`. -/
noncomputable def caratheodoryPicardCM
    (f : ℝ → E → E) (a b : ℝ) (hab : a ≤ b) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (x₀ : E)
    (h_int : ∀ γ : C(Icc a b, E),
      IntervalIntegrable (fun s ↦ f s (γ (projIcc a b hab s))) volume a b)
    (γ : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := x₀ + ∫ s in t₀..t.1, f s (γ (projIcc a b hab s))
  continuous_toFun := by
    have h_cont_int :
        ContinuousOn (fun t ↦ ∫ s in t₀..t, f s (γ (projIcc a b hab s))) (Icc a b) := by
      have ht₀_u : t₀ ∈ [[a, b]] := by rwa [uIcc_of_le hab]
      have h := intervalIntegral.continuousOn_primitive_interval' (h_int γ) ht₀_u
      rwa [uIcc_of_le hab] at h
    have h_cont_total :
        ContinuousOn (fun t ↦ x₀ + ∫ s in t₀..t, f s (γ (projIcc a b hab s))) (Icc a b) :=
      continuousOn_const.add h_cont_int
    exact h_cont_total.comp_continuous continuous_subtype_val Subtype.prop

@[simp]
theorem caratheodoryPicardCM_apply
    (f : ℝ → E → E) (a b : ℝ) (hab : a ≤ b) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (x₀ : E)
    (h_int : ∀ γ : C(Icc a b, E),
      IntervalIntegrable (fun s ↦ f s (γ (projIcc a b hab s))) volume a b)
    (γ : C(Icc a b, E)) (t : Icc a b) :
    caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ t =
      x₀ + ∫ s in t₀..t.1, f s (γ (projIcc a b hab s)) := rfl

/-- Distance estimate between two Picard iterates bounded by `(∫ ℓ) * dist γ₁ γ₂`.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 8.
- Carvalho-Neto, Frota, Torelli (2025), *A general version of Carathéodory theorem*, Eq. 7.
-/
theorem dist_caratheodoryPicardCM_le
    (f : ℝ → E → E) (ℓ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (x₀ : E)
    (h_int : ∀ γ : C(Icc a b, E),
      IntervalIntegrable (fun s ↦ f s (γ (projIcc a b hab s))) volume a b)
    (hlip : ∀ᵐ s ∂volume.restrict (Ι a b), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖)
    (hℓ : IntervalIntegrable ℓ volume a b)
    (hℓ_nonneg : ∀ᵐ s ∂volume.restrict (Ι a b), 0 ≤ ℓ s)
    (γ₁ γ₂ : C(Icc a b, E)) :
    dist (caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₁)
         (caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₂) ≤
      (∫ s in a..b, ℓ s) * dist γ₁ γ₂ := by
  have : Nonempty (Icc a b) := (nonempty_Icc.mpr hab).to_subtype
  have h_int_ℓ : 0 ≤ ∫ s in a..b, ℓ s := by
    rw [intervalIntegral.integral_of_le hab, ← uIoc_of_le hab]
    exact MeasureTheory.integral_nonneg_of_ae hℓ_nonneg
  have h_mul_nonneg : 0 ≤ (∫ s in a..b, ℓ s) * dist γ₁ γ₂ :=
    mul_nonneg h_int_ℓ dist_nonneg
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  rw [dist_eq_norm]
  have ht_mem : t.1 ∈ Icc a b := t.2
  have ht₀_u : t₀ ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have ht_u : t.1 ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have hsub_uIcc : [[t₀, t.1]] ⊆ [[a, b]] := uIcc_subset_uIcc ht₀_u ht_u
  have hsub_uIoc : Ι t₀ t.1 ⊆ Ι a b := uIoc_subset_uIoc_of_mem_Icc hab ht₀ ht_mem
  have h_int₁_sub : IntervalIntegrable (fun s ↦ f s (γ₁ (projIcc a b hab s))) volume t₀ t.1 :=
    (h_int γ₁).mono_set hsub_uIcc
  have h_int₂_sub : IntervalIntegrable (fun s ↦ f s (γ₂ (projIcc a b hab s))) volume t₀ t.1 :=
    (h_int γ₂).mono_set hsub_uIcc
  have hℓ_sub : IntervalIntegrable ℓ volume t₀ t.1 := hℓ.mono_set hsub_uIcc
  have hlip_sub : ∀ᵐ s ∂volume.restrict (Ι t₀ t.1), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖ :=
    ae_mono (Measure.restrict_mono hsub_uIoc le_rfl) hlip
  have hℓ_nonneg_sub : 0 ≤ᵐ[volume.restrict (Ι t₀ t.1)] ℓ :=
    ae_mono (Measure.restrict_mono hsub_uIoc le_rfl) hℓ_nonneg
  have h_le_dist : ∀ s, ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖ ≤ dist γ₁ γ₂ := by
    intro s
    rw [← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  have h_diff_cont : Continuous (fun s ↦ ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖) := by
    have h1 : Continuous (fun s ↦ γ₁ (projIcc a b hab s)) :=
      γ₁.continuous.comp continuous_projIcc
    have h2 : Continuous (fun s ↦ γ₂ (projIcc a b hab s)) :=
      γ₂.continuous.comp continuous_projIcc
    exact (h1.sub h2).norm
  have h_bound_int :
      IntervalIntegrable (fun s ↦ ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖)
        volume t₀ t.1 := by
    rw [intervalIntegrable_iff]
    have hℓ_int_on : IntegrableOn (fun s ↦ ℓ s * dist γ₁ γ₂) (Ι t₀ t.1) volume :=
      intervalIntegrable_iff.mp (hℓ_sub.mul_const (dist γ₁ γ₂))
    refine Integrable.mono' hℓ_int_on ?_ ?_
    · have hℓ_meas : AEStronglyMeasurable ℓ (volume.restrict (Ι t₀ t.1)) :=
        (intervalIntegrable_iff.mp hℓ_sub).aestronglyMeasurable
      have h_meas :
          AEStronglyMeasurable (fun s ↦ ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖)
            (volume.restrict (Ι t₀ t.1)) :=
        h_diff_cont.aestronglyMeasurable
      exact hℓ_meas.mul h_meas
    · filter_upwards [hℓ_nonneg_sub] with s hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
      refine mul_le_mul_of_nonneg_left ?_ hs
      rw [abs_of_nonneg (norm_nonneg _)]
      exact h_le_dist s
  have h_sub : (caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₁ t : E) -
      (caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₂ t : E) =
      ∫ s in t₀..t.1, (f s (γ₁ (projIcc a b hab s)) - f s (γ₂ (projIcc a b hab s))) := by
    simp only [caratheodoryPicardCM_apply]
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub h_int₁_sub h_int₂_sub]
  have h_norm_le : ‖(caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₁ t : E) -
      (caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₂ t : E)‖ ≤
      |∫ s in t₀..t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖| := by
    rw [h_sub]
    apply intervalIntegral.norm_integral_le_abs_of_norm_le _ h_bound_int
    filter_upwards [hlip_sub] with s hs
    exact hs (γ₁ (projIcc a b hab s)) (γ₂ (projIcc a b hab s))
  have h_integrand_nonneg : 0 ≤ᵐ[volume.restrict (Ι t₀ t.1)]
      (fun s ↦ ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖) := by
    filter_upwards [hℓ_nonneg_sub] with s hs
    exact mul_nonneg hs (norm_nonneg _)
  have h_abs_int_eq : |∫ s in t₀..t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖| =
      ∫ s in Ι t₀ t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖ := by
    rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc, abs_of_nonneg]
    exact MeasureTheory.integral_nonneg_of_ae h_integrand_nonneg
  have h_le_ae :
      (fun s ↦ ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖)
        ≤ᵐ[volume.restrict (Ι t₀ t.1)] (fun s ↦ ℓ s * dist γ₁ γ₂) := by
    filter_upwards [hℓ_nonneg_sub] with s hs
    exact mul_le_mul_of_nonneg_left (h_le_dist s) hs
  have h_step2 : ∫ s in Ι t₀ t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖ ≤
      ∫ s in Ι t₀ t.1, ℓ s * dist γ₁ γ₂ := by
    have h1 : IntegrableOn (fun s ↦ ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖)
        (Ι t₀ t.1) volume :=
      intervalIntegrable_iff.mp h_bound_int
    have h2 : IntegrableOn (fun s ↦ ℓ s * dist γ₁ γ₂) (Ι t₀ t.1) volume :=
      intervalIntegrable_iff.mp (hℓ_sub.mul_const (dist γ₁ γ₂))
    exact setIntegral_mono_ae_restrict h1 h2 h_le_ae
  have h_step3 : ∫ s in Ι t₀ t.1, ℓ s * dist γ₁ γ₂ ≤ ∫ s in Ι a b, ℓ s * dist γ₁ γ₂ := by
    have hℓD_nonneg : 0 ≤ᵐ[volume.restrict (Ι a b)] (fun s ↦ ℓ s * dist γ₁ γ₂) := by
      filter_upwards [hℓ_nonneg] with s hs
      exact mul_nonneg hs dist_nonneg
    have h_int_ab : IntegrableOn (fun s ↦ ℓ s * dist γ₁ γ₂) (Ι a b) volume :=
      intervalIntegrable_iff.mp (hℓ.mul_const (dist γ₁ γ₂))
    exact setIntegral_mono_set h_int_ab hℓD_nonneg hsub_uIoc.eventuallyLE
  have h_step4 : ∫ s in Ι a b, ℓ s * dist γ₁ γ₂ = (∫ s in a..b, ℓ s) * dist γ₁ γ₂ := by
    have h_uIoc_ab : Ι a b = Ioc a b := by rw [uIoc, min_eq_left hab, max_eq_right hab]
    rw [h_uIoc_ab, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_mul_const]
  calc ‖caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₁ t -
        caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int γ₂ t‖
       ≤ |∫ s in t₀..t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖| := h_norm_le
     _ = ∫ s in Ι t₀ t.1, ℓ s * ‖γ₁ (projIcc a b hab s) - γ₂ (projIcc a b hab s)‖ := h_abs_int_eq
     _ ≤ ∫ s in Ι t₀ t.1, ℓ s * dist γ₁ γ₂ := h_step2
     _ ≤ ∫ s in Ι a b, ℓ s * dist γ₁ γ₂ := h_step3
     _ = (∫ s in a..b, ℓ s) * dist γ₁ γ₂ := h_step4

/-- Local existence and uniqueness of Carathéodory solutions on an interval with small L¹ bound.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 8.
- Carvalho-Neto, Frota, Torelli (2025), *A general version of Carathéodory theorem*, Theorem 2.
-/
theorem exists_unique_caratheodory_solution_of_small_integral [CompleteSpace E]
    (f : ℝ → E → E) (ℓ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (x₀ : E)
    (h_int : ∀ γ : C(Icc a b, E),
      IntervalIntegrable (fun s ↦ f s (γ (projIcc a b hab s))) volume a b)
    (hlip : ∀ᵐ s ∂volume.restrict (Ι a b), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖)
    (hℓ : IntervalIntegrable ℓ volume a b)
    (hℓ_nonneg : ∀ᵐ s ∂volume.restrict (Ι a b), 0 ≤ ℓ s)
    (h_small : (∫ s in a..b, ℓ s) < 1) :
    ∃! γ : C(Icc a b, E),
      IsCaratheodorySolutionOn (fun t ↦ γ (projIcc a b hab t)) f t₀ x₀ (Icc a b) := by
  have : Nonempty (Icc a b) := (nonempty_Icc.mpr hab).to_subtype
  have h_int_ℓ : 0 ≤ ∫ s in a..b, ℓ s := by
    rw [intervalIntegral.integral_of_le hab, ← uIoc_of_le hab]
    exact MeasureTheory.integral_nonneg_of_ae hℓ_nonneg
  set K : ℝ≥0 := ⟨∫ s in a..b, ℓ s, h_int_ℓ⟩ with hK_def
  have hK_lt : K < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact h_small
  set T := caratheodoryPicardCM f a b hab t₀ ht₀ x₀ h_int
  have h_lip : LipschitzWith K T := by
    refine LipschitzWith.of_dist_le_mul fun γ₁ γ₂ ↦ ?_
    exact dist_caratheodoryPicardCM_le f ℓ a b hab t₀ ht₀ x₀ h_int hlip hℓ hℓ_nonneg γ₁ γ₂
  have h_contr : ContractingWith K T := ⟨hK_lt, h_lip⟩
  have : Nonempty C(Icc a b, E) := inferInstance
  set γ_fix := h_contr.fixedPoint T with h_fix_def
  have h_is_fix : IsFixedPt T γ_fix := h_contr.fixedPoint_isFixedPt
  refine ⟨γ_fix, ?_, ?_⟩
  · intro t ht
    change γ_fix (projIcc a b hab t) = x₀ + ∫ s in t₀..t, f s (γ_fix (projIcc a b hab s))
    have ht_proj : projIcc a b hab t = ⟨t, ht⟩ := projIcc_of_mem hab ht
    rw [ht_proj]
    have h_eval : γ_fix ⟨t, ht⟩ = (T γ_fix) ⟨t, ht⟩ := by rw [h_is_fix]
    rw [h_eval, caratheodoryPicardCM_apply]
  · intro γ' hγ'_sol
    have hγ'_fix : IsFixedPt T γ' := by
      ext t
      rw [caratheodoryPicardCM_apply]
      have ht_mem : t.1 ∈ Icc a b := t.2
      have ht_proj : projIcc a b hab t.1 = t :=
        (projIcc_of_mem hab ht_mem).trans (Subtype.ext rfl)
      have h_sol_t := hγ'_sol t.1 ht_mem
      dsimp only at h_sol_t
      rw [ht_proj] at h_sol_t
      exact h_sol_t.symm
    exact h_contr.fixedPoint_unique hγ'_fix

/-- Uniqueness of any two Carathéodory solutions on an interval with small L¹ bound.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 8.
- Carvalho-Neto et al. (2025), *A general version of Carathéodory theorem*, Theorem 2.
-/
theorem isCaratheodorySolutionOn_unique_of_small_integral
    {f : ℝ → E → E} {ℓ : ℝ → ℝ} {t₀ a b : ℝ} {x₀ : E} {γ₁ γ₂ : ℝ → E}
    (hab : a ≤ b)
    (ht₀ : t₀ ∈ Icc a b)
    (hsol₁ : IsCaratheodorySolutionOn γ₁ f t₀ x₀ (Icc a b))
    (hsol₂ : IsCaratheodorySolutionOn γ₂ f t₀ x₀ (Icc a b))
    (hcont₁ : ContinuousOn γ₁ (Icc a b))
    (hcont₂ : ContinuousOn γ₂ (Icc a b))
    (hlip : ∀ᵐ s ∂volume.restrict (Ι a b), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖)
    (h_int₁ : IntervalIntegrable (fun τ ↦ f τ (γ₁ τ)) volume a b)
    (h_int₂ : IntervalIntegrable (fun τ ↦ f τ (γ₂ τ)) volume a b)
    (hℓ : IntervalIntegrable ℓ volume a b)
    (hℓ_nonneg : ∀ᵐ s ∂volume.restrict (Ι a b), 0 ≤ ℓ s)
    (h_small : (∫ s in a..b, ℓ s) < 1) :
    EqOn γ₁ γ₂ (Icc a b) := by
  have hg_cont : ContinuousOn (fun t ↦ ‖γ₁ t - γ₂ t‖) (Icc a b) :=
    (hcont₁.sub hcont₂).norm
  obtain ⟨t_max, ht_max_mem, ht_max⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hg_cont
  set M := ‖γ₁ t_max - γ₂ t_max‖ with hM_def
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have h_le_M : ∀ t ∈ Icc a b, ‖γ₁ t - γ₂ t‖ ≤ M := fun t ht ↦ ht_max ht
  have ht₀_u : t₀ ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have ht_max_u : t_max ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have hsub_uIcc : [[t₀, t_max]] ⊆ [[a, b]] := uIcc_subset_uIcc ht₀_u ht_max_u
  have hsub_uIoc : Ι t₀ t_max ⊆ Ι a b := uIoc_subset_uIoc_of_mem_Icc hab ht₀ ht_max_mem
  have hsub_Icc : Ι t₀ t_max ⊆ Icc a b := uIoc_subset_Icc_of_mem_Icc ht₀ ht_max_mem
  have hlip_sub : ∀ᵐ s ∂volume.restrict (Ι t₀ t_max), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖ :=
    ae_mono (Measure.restrict_mono hsub_uIoc le_rfl) hlip
  have hℓ_nonneg_sub : 0 ≤ᵐ[volume.restrict (Ι t₀ t_max)] ℓ :=
    ae_mono (Measure.restrict_mono hsub_uIoc le_rfl) hℓ_nonneg
  have h_int₁_sub : IntervalIntegrable (fun τ ↦ f τ (γ₁ τ)) volume t₀ t_max :=
    h_int₁.mono_set hsub_uIcc
  have h_int₂_sub : IntervalIntegrable (fun τ ↦ f τ (γ₂ τ)) volume t₀ t_max :=
    h_int₂.mono_set hsub_uIcc
  have hℓ_sub : IntervalIntegrable ℓ volume t₀ t_max :=
    hℓ.mono_set hsub_uIcc
  have h_meas_diff :
      AEStronglyMeasurable (fun τ ↦ ‖γ₁ τ - γ₂ τ‖) (volume.restrict (Ι t₀ t_max)) :=
    (hg_cont.mono hsub_Icc).aestronglyMeasurable measurableSet_uIoc
  have h_bound_int : IntervalIntegrable (fun τ ↦ ℓ τ * ‖γ₁ τ - γ₂ τ‖) volume t₀ t_max := by
    rw [intervalIntegrable_iff]
    have hℓ_int_on : IntegrableOn (fun s ↦ ℓ s * M) (Ι t₀ t_max) volume :=
      intervalIntegrable_iff.mp (hℓ_sub.mul_const M)
    refine Integrable.mono' hℓ_int_on ?_ ?_
    · have hℓ_meas : AEStronglyMeasurable ℓ (volume.restrict (Ι t₀ t_max)) :=
        (intervalIntegrable_iff.mp hℓ_sub).aestronglyMeasurable
      exact hℓ_meas.mul h_meas_diff
    · filter_upwards [hℓ_nonneg_sub, ae_restrict_mem measurableSet_uIoc] with s hs hs_mem
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
      refine mul_le_mul_of_nonneg_left ?_ hs
      rw [abs_of_nonneg (norm_nonneg _)]
      exact h_le_M s (hsub_Icc hs_mem)
  have h_step : M ≤ |∫ s in t₀..t_max, ℓ s * ‖γ₁ s - γ₂ s‖| := by
    have h1 := hsol₁ t_max ht_max_mem
    have h2 := hsol₂ t_max ht_max_mem
    have h_sub : γ₁ t_max - γ₂ t_max =
        ∫ τ in t₀..t_max, (f τ (γ₁ τ) - f τ (γ₂ τ)) := by
      rw [h1, h2, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub h_int₁_sub h_int₂_sub]
    rw [hM_def, h_sub]
    apply intervalIntegral.norm_integral_le_abs_of_norm_le _ h_bound_int
    filter_upwards [hlip_sub] with s hs
    exact hs (γ₁ s) (γ₂ s)
  have h_integrand_nonneg : 0 ≤ᵐ[volume.restrict (Ι t₀ t_max)]
      (fun s ↦ ℓ s * ‖γ₁ s - γ₂ s‖) := by
    filter_upwards [hℓ_nonneg_sub] with s hs
    exact mul_nonneg hs (norm_nonneg _)
  have h_abs_int_eq : |∫ s in t₀..t_max, ℓ s * ‖γ₁ s - γ₂ s‖| =
      ∫ s in Ι t₀ t_max, ℓ s * ‖γ₁ s - γ₂ s‖ := by
    rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc, abs_of_nonneg]
    exact MeasureTheory.integral_nonneg_of_ae h_integrand_nonneg
  have h_le_ae : (fun s ↦ ℓ s * ‖γ₁ s - γ₂ s‖) ≤ᵐ[volume.restrict (Ι t₀ t_max)]
      (fun s ↦ ℓ s * M) := by
    filter_upwards [hℓ_nonneg_sub, ae_restrict_mem measurableSet_uIoc] with s hs hs_mem
    exact mul_le_mul_of_nonneg_left (h_le_M s (hsub_Icc hs_mem)) hs
  have h_step2 : ∫ s in Ι t₀ t_max, ℓ s * ‖γ₁ s - γ₂ s‖ ≤ ∫ s in Ι t₀ t_max, ℓ s * M := by
    have h1 : IntegrableOn (fun τ ↦ ℓ τ * ‖γ₁ τ - γ₂ τ‖) (Ι t₀ t_max) volume :=
      intervalIntegrable_iff.mp h_bound_int
    have h2 : IntegrableOn (fun τ ↦ ℓ τ * M) (Ι t₀ t_max) volume :=
      intervalIntegrable_iff.mp (hℓ_sub.mul_const M)
    exact setIntegral_mono_ae_restrict h1 h2 h_le_ae
  have h_step3 : ∫ s in Ι t₀ t_max, ℓ s * M ≤ ∫ s in Ι a b, ℓ s * M := by
    have hℓM_nonneg : 0 ≤ᵐ[volume.restrict (Ι a b)] (fun s ↦ ℓ s * M) := by
      filter_upwards [hℓ_nonneg] with s hs
      exact mul_nonneg hs hM_nonneg
    have h_int_ab : IntegrableOn (fun s ↦ ℓ s * M) (Ι a b) volume :=
      intervalIntegrable_iff.mp (hℓ.mul_const M)
    exact setIntegral_mono_set h_int_ab hℓM_nonneg hsub_uIoc.eventuallyLE
  have h_step4 : ∫ s in Ι a b, ℓ s * M = (∫ s in a..b, ℓ s) * M := by
    have h_uIoc_ab : Ι a b = Ioc a b := by rw [uIoc, min_eq_left hab, max_eq_right hab]
    rw [h_uIoc_ab, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_mul_const]
  have hM_le : M ≤ (∫ s in a..b, ℓ s) * M := by
    calc M ≤ |∫ s in t₀..t_max, ℓ s * ‖γ₁ s - γ₂ s‖| := h_step
         _ = ∫ s in Ι t₀ t_max, ℓ s * ‖γ₁ s - γ₂ s‖ := h_abs_int_eq
         _ ≤ ∫ s in Ι t₀ t_max, ℓ s * M := h_step2
         _ ≤ ∫ s in Ι a b, ℓ s * M := h_step3
         _ = (∫ s in a..b, ℓ s) * M := h_step4
  have hM_zero : M = 0 := le_of_mul_le_mul_right_zero hM_nonneg h_small hM_le
  intro t ht
  have : ‖γ₁ t - γ₂ t‖ ≤ 0 := by
    calc ‖γ₁ t - γ₂ t‖ ≤ M := h_le_M t ht
         _ = 0 := hM_zero
  have : ‖γ₁ t - γ₂ t‖ = 0 := le_antisymm this (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

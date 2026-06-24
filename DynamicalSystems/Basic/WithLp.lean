/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # `WithLp` and `eLpNorm`

-/


@[expose] public noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

variable {α ε ε' 𝕜 𝕜' E F V W : Type*} {m : MeasurableSpace α} {p p' : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [ENorm ε] [ENorm ε']

theorem eLpNormEssSup_mono_enorm_ae' {f : α → ε} {g : α → ε'} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg


namespace WithLp

def copy (f : WithLp p V) (p' : ℝ≥0∞) : WithLp p' V := toLp p' (ofLp f)

@[simp]
theorem copy_toLp {f : V} {p' : ℝ≥0∞} : (toLp p f).copy p' = toLp p' f := rfl

@[simp]
theorem ofLp_copy {f : WithLp p V} {p' : ℝ≥0∞} : ofLp (f.copy p') = ofLp f := rfl

@[simp]
theorem fst_copy {f : WithLp p (V × W)} {p' : ℝ≥0∞} : (f.copy p').fst = f.fst := rfl

@[simp]
theorem snd_copy {f : WithLp p (V × W)} {p' : ℝ≥0∞} : (f.copy p').snd = f.snd := rfl

theorem norm_copy {f : WithLp p (E × F)} (h : p = p') :
      ‖f.copy p'‖ = ‖f‖ := by
    rw [← h]
    rfl

theorem ennnorm_copy {f : WithLp p (E × F)} [hp : Fact (1 ≤ p)] [hp : Fact (1 ≤ p')] (h : p = p') :
      ‖f.copy p'‖ₑ = ‖f‖ₑ := by
    refine enorm_eq_iff_norm_eq.mpr ?_
    exact norm_copy h

theorem prod_enorm_eq_sup (f : WithLp ∞ (E × F)) : ‖f‖ₑ = ‖f.fst‖ₑ ⊔ ‖f.snd‖ₑ := rfl


end WithLp

namespace MeasureTheory

variable {f : α → E} {g : α → F}

theorem eLpNorm_withLp_prod [hp : Fact (1 ≤ p)] (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ) ^ p.toReal =
    (eLpNorm f p μ) ^ p.toReal + (eLpNorm g p μ) ^ p.toReal := by
  have hp'' : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp'
  have hp''' : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.out).ne'
  simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp''' hp']
  simp_rw [← ENNReal.rpow_mul]
  simp_rw [one_div_mul_cancel hp''.ne']
  simp only [ENNReal.rpow_one]
  rw [← lintegral_add_left' (by fun_prop)]
  congr; ext x
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp_rw [← ENNReal.toReal_rpow]
  simp only [toReal_enorm]
  rw [WithLp.prod_norm_eq_add hp'']
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp''.ne']
  simp

theorem eLpNorm_withLp_prod' [hp : Fact (1 ≤ p)] (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ =
    ((eLpNorm f p μ) ^ p.toReal + (eLpNorm g p μ) ^ p.toReal) ^ (1 / p.toReal) := by
  have hp'' : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp'
  have hp''' : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.out).ne'
  simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp''' hp']
  simp_rw [← ENNReal.rpow_mul]
  simp_rw [one_div_mul_cancel hp''.ne']
  simp only [ENNReal.rpow_one]
  congr 1
  rw [← lintegral_add_left' (by fun_prop)]
  congr; ext x
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp_rw [← ENNReal.toReal_rpow]
  simp only [toReal_enorm]
  rw [WithLp.prod_norm_eq_add hp'']
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp''.ne']
  simp

theorem eLpNorm_withLp_prod_le_add [hp : Fact (1 ≤ p)] (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  by_cases! hp' : p ≠ ∞
  · calc
      _ = ((eLpNorm f p μ) ^ p.toReal + (eLpNorm g p μ) ^ p.toReal) ^ (1 / p.toReal) :=
        eLpNorm_withLp_prod' hp' hf
      _ ≤ _ := by
        apply ENNReal.rpow_add_rpow_le_add
        simp [← ENNReal.ofReal_le_iff_le_toReal hp', hp.out]
  · unfold eLpNorm
    simp only [hp', ENNReal.top_ne_zero, ↓reduceIte]
    apply MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound
    simp only [← WithLp.ennnorm_copy hp', WithLp.copy_toLp, WithLp.prod_enorm_eq_sup,
      WithLp.toLp_fst, WithLp.toLp_snd, sup_le_iff, eventually_and]
    constructor
    · filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := f)]  with x hx
      grw [hx]
      simp
    · filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := g)] with x hx
      grw [hx]
      simp

def addLEConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = ∞ then 2 else 2 ^ ((p.toReal - 1) / p.toReal)

theorem addLEConst_of_ne {p : ℝ≥0∞} (hp : p ≠ ∞) :
    addLEConst p = 2 ^ ((p.toReal - 1) / p.toReal) := by
  simp [addLEConst, hp]

@[simp]
theorem addLEConst_infty :
    addLEConst ∞ = 2 := by
  simp [addLEConst]

@[simp]
theorem addLEConst_ne_top {p : ℝ≥0∞} : addLEConst p ≠ ∞ := by
  by_cases! hp : p ≠ ∞
  · simp [addLEConst_of_ne hp]
  · simp [hp]

theorem add_le_eLpNorm_withLp_prod [hp : Fact (1 ≤ p)] --(hp' : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ + eLpNorm g p μ ≤ addLEConst p *
      eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ := by
  by_cases! hp' : p ≠ ∞
  · calc
    _ = ((eLpNorm f p μ + eLpNorm g p μ) ^ p.toReal) ^ (1 / p.toReal) := by
      have hp'' : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp'
      rw [← ENNReal.rpow_mul]
      rw [mul_one_div_cancel hp''.ne']
      simp
    _ ≤ ((2 : ℝ≥0∞) ^ (p.toReal - 1) *
        ((eLpNorm f p μ) ^ p.toReal + (eLpNorm g p μ) ^ p.toReal)) ^ (1 / p.toReal) := by
      gcongr
      apply ENNReal.rpow_add_le_mul_rpow_add_rpow
      simp [← ENNReal.ofReal_le_iff_le_toReal hp', hp.out]
    _ = ((2 : ℝ≥0∞) ^ (p.toReal - 1) *
        (eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ) ^ p.toReal) ^ (1 / p.toReal) := by
      rw [← eLpNorm_withLp_prod hp' hf]
    _ = _ := by
      have hp'' : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp'
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp''.ne', mul_one_div]
      simp [addLEConst_of_ne hp']
  · simp only [hp', eLpNorm_exponent_top, addLEConst_infty, two_mul]
    gcongr
    · apply eLpNormEssSup_mono_enorm_ae'
      filter_upwards with x
      refine enorm_le_iff_norm_le.mpr ?_
      convert! WithLp.norm_fst_le _ (WithLp.toLp p (f x, g x))
    · apply eLpNormEssSup_mono_enorm_ae'
      filter_upwards with x
      refine enorm_le_iff_norm_le.mpr ?_
      convert! WithLp.norm_snd_le _ (WithLp.toLp p (f x, g x))


end MeasureTheory

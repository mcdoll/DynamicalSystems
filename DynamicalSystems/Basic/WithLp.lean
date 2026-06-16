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

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

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

theorem eLpNorm_withLp_prod_le_add [hp : Fact (1 ≤ p)] (hp' : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := calc
  _ = ((eLpNorm f p μ) ^ p.toReal + (eLpNorm g p μ) ^ p.toReal) ^ (1 / p.toReal) :=
    eLpNorm_withLp_prod' hp' hf
  _ ≤ _ := by
    apply ENNReal.rpow_add_rpow_le_add
    simp [← ENNReal.ofReal_le_iff_le_toReal hp', hp.out]

theorem add_le_eLpNorm_withLp_prod [hp : Fact (1 ≤ p)] (hp' : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ + eLpNorm g p μ ≤ (2 : ℝ≥0∞) ^ ((p.toReal - 1) / p.toReal) *
      eLpNorm (fun x ↦ WithLp.toLp p (f x, g x)) p μ := calc
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
    simp


end MeasureTheory

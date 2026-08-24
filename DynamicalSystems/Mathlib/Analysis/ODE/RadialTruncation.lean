/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.ODE.Basic

/-!
# Radial truncation (radial retraction onto a closed ball)

For `R ≥ 0`, the map `radialTrunc R` is the radial retraction of a normed space onto the
closed ball of radius `R` centred at the origin: it is the identity on the ball, and it
sends a point `x` outside the ball to the point `(R / ‖x‖) • x` on the sphere.

The key fact is that this map is Lipschitz with constant `2` in an arbitrary normed space
(`lipschitzWith_radialTrunc`).  It is used to truncate a vector field of linear growth into
a bounded one.
-/

public section

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction onto the closed ball of radius `R` about the origin. -/
noncomputable def radialTrunc (R : ℝ) (x : E) : E :=
  if ‖x‖ ≤ R then x else (R / ‖x‖) • x

lemma radialTrunc_eq_self {R : ℝ} {x : E} (hx : ‖x‖ ≤ R) : radialTrunc R x = x :=
  ite_eq_left hx

lemma norm_radialTrunc_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖radialTrunc R x‖ ≤ R := by
  unfold radialTrunc
  split_ifs with h
  · exact h
  · push Not at h
    have hx : 0 < ‖x‖ := lt_of_le_of_lt hR h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_mul_cancel₀ _ hx.ne']

lemma norm_radialTrunc_le_self {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖radialTrunc R x‖ ≤ ‖x‖ := by
  unfold radialTrunc
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have hx : 0 < ‖x‖ := lt_of_le_of_lt hR h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hx.ne']
    exact h.le

/-- The radial retraction onto a ball of radius `R ≥ 0` moves points by at most twice their
distance: it is `2`-Lipschitz. -/
lemma norm_radialTrunc_sub_radialTrunc_le {R : ℝ} (hR : 0 ≤ R) (x y : E) :
    ‖radialTrunc R x - radialTrunc R y‖ ≤ 2 * ‖x - y‖ := by
  wlog hxy : ‖y‖ ≤ ‖x‖ generalizing x y
  · have h := this y x (le_of_not_ge hxy)
    rw [norm_sub_rev (radialTrunc R x), norm_sub_rev x]
    exact h
  have hd : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  rcases le_or_gt ‖x‖ R with hxR | hxR
  · rw [radialTrunc_eq_self hxR, radialTrunc_eq_self (hxy.trans hxR)]
    nlinarith [norm_nonneg (x - y)]
  · have hx0 : 0 < ‖x‖ := lt_of_le_of_lt hR hxR
    rw [show radialTrunc R x = (R / ‖x‖) • x from ite_eq_right (not_le.mpr hxR)]
    set t : ℝ := R / ‖x‖ with ht
    have ht0 : 0 ≤ t := by positivity
    have htx : t * ‖x‖ = R := by rw [ht, div_mul_cancel₀ _ hx0.ne']
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hx0]; linarith
    rcases le_or_gt ‖y‖ R with hyR | hyR
    · rw [radialTrunc_eq_self hyR]
      have hdecomp : t • x - y = t • (x - y) + (t - 1) • y := by module
      have e1 : ‖t • (x - y)‖ = t * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      have e2 : ‖(t - 1) • y‖ = (1 - t) * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have h4 : (1 - t) * R ≤ ‖x‖ - R := by nlinarith [sq_nonneg (1 - t)]
      have h5 : (1 - t) * ‖y‖ ≤ (1 - t) * R :=
        mul_le_mul_of_nonneg_left hyR (by linarith)
      have h6 : t * ‖x - y‖ ≤ ‖x - y‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht1
      calc ‖t • x - y‖ = ‖t • (x - y) + (t - 1) • y‖ := by rw [hdecomp]
        _ ≤ ‖t • (x - y)‖ + ‖(t - 1) • y‖ := norm_add_le _ _
        _ = t * ‖x - y‖ + (1 - t) * ‖y‖ := by rw [e1, e2]
        _ ≤ 2 * ‖x - y‖ := by linarith
    · have hy0 : 0 < ‖y‖ := lt_of_le_of_lt hR hyR
      rw [show radialTrunc R y = (R / ‖y‖) • y from ite_eq_right (not_le.mpr hyR)]
      set s : ℝ := R / ‖y‖ with hs
      have hsy : s * ‖y‖ = R := by rw [hs, div_mul_cancel₀ _ hy0.ne']
      have hts : t ≤ s := by
        rw [ht, hs]
        gcongr
      have hdecomp : t • x - s • y = t • (x - y) + (t - s) • y := by module
      have e1 : ‖t • (x - y)‖ = t * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      have e2 : ‖(t - s) • y‖ = (s - t) * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have h4 : (s - t) * ‖y‖ ≤ ‖x‖ - ‖y‖ := by
        have hmul : ((s - t) * ‖y‖) * ‖x‖ ≤ (‖x‖ - ‖y‖) * ‖x‖ := by
          have hexp : ((s - t) * ‖y‖) * ‖x‖ = R * ‖x‖ - R * ‖y‖ := by
            have : s * ‖y‖ = R := hsy
            nlinarith [htx, hsy]
          nlinarith [htx]
        exact le_of_mul_le_mul_right hmul hx0
      have h6 : t * ‖x - y‖ ≤ ‖x - y‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht1
      calc ‖t • x - s • y‖ = ‖t • (x - y) + (t - s) • y‖ := by rw [hdecomp]
        _ ≤ ‖t • (x - y)‖ + ‖(t - s) • y‖ := norm_add_le _ _
        _ = t * ‖x - y‖ + (s - t) * ‖y‖ := by rw [e1, e2]
        _ ≤ 2 * ‖x - y‖ := by linarith

lemma lipschitzWith_radialTrunc {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 2 (radialTrunc R : E → E) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [dist_eq_norm] using norm_radialTrunc_sub_radialTrunc_le hR x y

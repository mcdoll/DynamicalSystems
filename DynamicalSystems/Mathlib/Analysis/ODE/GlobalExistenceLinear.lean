/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
public import DynamicalSystems.Basic.NonAutonomous
import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique

import DynamicalSystems.Mathlib.Analysis.ODE.RadialTruncation

/-!
# Global existence for ODEs with a globally Lipschitz vector field of linear growth

-/

open scoped NNReal
open Metric Set

/-! ## Global existence -/

section GlobalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {C C' : ℝ} {K : ℝ≥0}

/-- Existence on an arbitrarily large compact time interval for a *bounded* vector field,
from the Picard-Lindelöf theorem. -/
theorem exists_solution_Icc (h_lip : ∀ t, LipschitzWith K (f t))
    (h_cont : ∀ x, Continuous (f · x)) (h_bdd : ∀ t x, ‖f t x‖ ≤ C)
    (t₀ : ℝ) (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t ∈ Icc (t₀ - R) (t₀ + R),
      HasDerivWithinAt α (f t (α t)) (Icc (t₀ - R) (t₀ + R)) t := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (h_bdd 0 0)
  have ht₀ : t₀ ∈ Icc (t₀ - R) (t₀ + R) := ⟨by linarith, by linarith⟩
  have hpl : IsPicardLindelof f (tmin := t₀ - R) (tmax := t₀ + R) ⟨t₀, ht₀⟩ x₀
      ⟨C * R, by positivity⟩ 0 ⟨C, hC⟩ K := by
    refine ⟨fun t _ ↦ (h_lip t).lipschitzOnWith, fun x _ ↦ (h_cont x).continuousOn,
      fun t _ x _ ↦ h_bdd t x, ?_⟩
    change (C : ℝ) * max (t₀ + R - t₀) (t₀ - (t₀ - R)) ≤ (C * R : ℝ) - ((0 : ℝ≥0) : ℝ)
    rw [show t₀ + R - t₀ = R by ring, show t₀ - (t₀ - R) = R by ring, max_self]
    simp
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

omit [CompleteSpace E] in
/-- Two solutions with the same initial condition agree on any open interval on which
they are both defined. -/
theorem solution_eqOn_Ioo (h_lip : ∀ t, LipschitzWith K (f t))
    {α β : ℝ → E} {t₀ a b : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f t (α t)) t)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (f t (β t)) t) :
    EqOn α β (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (K := K) (s := fun _ ↦ univ)
    (fun t _ ↦ (h_lip t).lipschitzOnWith) ht₀
    (fun t ht ↦ ⟨hα t ht, trivial⟩) (fun t ht ↦ ⟨hβ t ht, trivial⟩) hαβ

omit [CompleteSpace E] in
/-- Solutions on arbitrarily large compact time intervals can be patched into a single global
solution. -/
theorem exists_global_of_exists_solution_Icc (h_lip : ∀ t, LipschitzWith K (f t))
    (H : ∀ (t₀ : ℝ) (x₀ : E) (R : ℝ), 0 ≤ R → ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - R) (t₀ + R), HasDerivWithinAt α (f t (α t)) (Icc (t₀ - R) (t₀ + R)) t) :
    ∃ Φ : ℝ → E → ℝ → E, ∀ t₀ x₀, IsIntegralCurve (Φ t₀ x₀) f ∧ Φ t₀ x₀ t₀ = x₀ := by
  -- For each initial condition and each `n : ℕ`, a solution on `[t₀ - (n+1), t₀ + (n+1)]`.
  have H' : ∀ (t₀ : ℝ) (x₀ : E) (n : ℕ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1)),
        HasDerivWithinAt α (f t (α t)) (Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1))) t :=
    fun t₀ x₀ n ↦ H t₀ x₀ ((n : ℝ) + 1) (by positivity)
  choose α hα0 hα using H'
  -- At interior times these are genuine solutions.
  have hderiv : ∀ (t₀ : ℝ) (x₀ : E) (n : ℕ) (t : ℝ), |t - t₀| < (n : ℝ) + 1 →
      HasDerivAt (α t₀ x₀ n) (f t (α t₀ x₀ n t)) t := by
    intro t₀ x₀ n t ht
    rw [abs_lt] at ht
    obtain ⟨h1, h2⟩ := ht
    exact (hα t₀ x₀ n t ⟨by linarith, by linarith⟩).hasDerivAt
      (Icc_mem_nhds (by linarith) (by linarith))
  -- Solutions for different `n` agree wherever both are defined.
  have hagree : ∀ (t₀ : ℝ) (x₀ : E) (m n : ℕ), m ≤ n → ∀ t : ℝ, |t - t₀| < (m : ℝ) + 1 →
      α t₀ x₀ m t = α t₀ x₀ n t := by
    intro t₀ x₀ m n hmn t ht
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hsub : ∀ s ∈ Ioo (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)), |s - t₀| < (m : ℝ) + 1 := by
      intro s hs
      rw [abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    refine solution_eqOn_Ioo (t₀ := t₀) h_lip (a := t₀ - ((m : ℝ) + 1)) (b := t₀ + ((m : ℝ) + 1))
      ⟨by linarith, by linarith⟩
      ((hα0 _ _ _).trans (hα0 _ _ _).symm)
      (fun s hs ↦ hderiv t₀ x₀ m s (hsub s hs))
      (fun s hs ↦ hderiv t₀ x₀ n s ((hsub s hs).trans_le (by linarith))) ?_
    rw [abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t₀ x₀ t ↦ α t₀ x₀ ⌈|t - t₀|⌉₊ t, fun t₀ x₀ ↦ ⟨fun t ↦ ?_, by simp [hα0]⟩⟩
  set N : ℕ := ⌈|t - t₀|⌉₊ with hN
  have hNle : |t - t₀| ≤ (N : ℝ) := Nat.le_ceil _
  -- Near `t`, the constructed flow coincides with the single solution of index `N + 1`.
  have key : ∀ s : ℝ, |s - t| < 1 / 2 → α t₀ x₀ ⌈|s - t₀|⌉₊ s = α t₀ x₀ (N + 1) s := by
    intro s hs
    have hst : |s - t₀| ≤ (N : ℝ) + 1 / 2 := by
      calc |s - t₀| ≤ |s - t| + |t - t₀| := by
            simpa using abs_sub_le s t t₀
        _ ≤ (N : ℝ) + 1 / 2 := by linarith
    refine hagree t₀ x₀ _ (N + 1) ?_ s ?_
    · refine Nat.ceil_le.mpr ?_
      push_cast
      linarith
    · exact lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
  have hev : (fun s ↦ α t₀ x₀ ⌈|s - t₀|⌉₊ s) =ᶠ[nhds t] α t₀ x₀ (N + 1) := by
    have hball : ∀ᶠ s in nhds t, |s - t| < 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      simpa [Real.dist_eq] using hs
    filter_upwards [hball] with s hs using key s hs
  have hval : α t₀ x₀ N t = α t₀ x₀ (N + 1) t := by
    simpa using key t (by norm_num)
  have hd : HasDerivAt (α t₀ x₀ (N + 1)) (f t (α t₀ x₀ (N + 1) t)) t := by
    refine hderiv t₀ x₀ (N + 1) t ?_
    push_cast
    linarith
  change HasDerivAt (fun s ↦ α t₀ x₀ ⌈|s - t₀|⌉₊ s) (f t (α t₀ x₀ N t)) t
  rw [hval]
  exact hd.congr_of_eventuallyEq hev

omit [CompleteSpace E] in
/-- A priori bound (Grönwall): a solution of a vector field with linear growth
`‖f t x‖ ≤ C * ‖x‖ + C'` on `[t₀ - T, t₀ + T]` stays in a ball whose radius depends only on
`‖α t₀‖`, `C`, `C'` and `T`. -/
theorem norm_le_gronwallBound_of_linear_growth (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h_bdd : ∀ t x, ‖f t x‖ ≤ C * ‖x‖ + C') {α : ℝ → E} {t₀ T : ℝ} (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivWithinAt α (f t (α t)) (Icc (t₀ - T) (t₀ + T)) t) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖α t‖ ≤ gronwallBound ‖α t₀‖ C C' T := by
  have hcont : ContinuousOn α (Icc (t₀ - T) (t₀ + T)) := fun t ht ↦ (hα t ht).continuousWithinAt
  have hint : ∀ t ∈ Ioo (t₀ - T) (t₀ + T), HasDerivAt α (f t (α t)) t := fun t ht ↦
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hmono : ∀ x ≤ T, gronwallBound ‖α t₀‖ C C' x ≤ gronwallBound ‖α t₀‖ C C' T :=
    fun x hx ↦ gronwallBound_mono (norm_nonneg _) hC' hC hx
  -- Forward in time.
  have hfwd : ∀ t ∈ Icc t₀ (t₀ + T), ‖α t‖ ≤ gronwallBound ‖α t₀‖ C C' (t - t₀) := by
    refine norm_le_gronwallBound_of_norm_deriv_right_le (f' := fun t ↦ f t (α t))
      (hcont.mono (fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩)) (fun x hx ↦ ?_) le_rfl
      (fun x _ ↦ h_bdd x (α x))
    exact (hint x ⟨by linarith [hx.1, hx.2], hx.2⟩).hasDerivWithinAt
  -- Backward in time, by reflecting the time variable about `t₀`.
  have hbwd : ∀ s ∈ Icc t₀ (t₀ + T), ‖α (2 * t₀ - s)‖ ≤ gronwallBound ‖α t₀‖ C C' (s - t₀) := by
    have hmem : MapsTo (fun s : ℝ ↦ 2 * t₀ - s) (Icc t₀ (t₀ + T)) (Icc (t₀ - T) (t₀ + T)) := by
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hβcont : ContinuousOn (fun s ↦ α (2 * t₀ - s)) (Icc t₀ (t₀ + T)) :=
      hcont.comp (by fun_prop) hmem
    refine norm_le_gronwallBound_of_norm_deriv_right_le
      (f' := fun s ↦ -(f (2 * t₀ - s) (α (2 * t₀ - s)))) hβcont (fun s hs ↦ ?_)
      (by rw [show 2 * t₀ - t₀ = t₀ by ring]) (fun s _ ↦ by simpa using h_bdd _ _)
    have h1 : HasDerivAt (fun s : ℝ ↦ 2 * t₀ - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (2 * t₀)
    have h2 : HasDerivAt α (f (2 * t₀ - s) (α (2 * t₀ - s))) (2 * t₀ - s) :=
      hint _ ⟨by linarith [hs.2], by linarith [hs.1, hs.2]⟩
    have h3 := h2.scomp s h1
    convert h3.hasDerivWithinAt
    · simp
    · simp
  intro t ht
  rcases le_or_gt t₀ t with h | h
  · exact (hfwd t ⟨h, ht.2⟩).trans (hmono _ (by linarith [ht.2]))
  · have hs : 2 * t₀ - t ∈ Icc t₀ (t₀ + T) := ⟨by linarith, by linarith [ht.1]⟩
    have hb := hbwd _ hs
    rw [show 2 * t₀ - (2 * t₀ - t) = t by ring] at hb
    exact hb.trans (hmono _ (by linarith [ht.1]))

/-- Existence on an arbitrarily large compact time interval for a globally Lipschitz vector
field with linear growth. -/
theorem exists_solution_Icc_of_linear_growth (h_lip : ∀ t, LipschitzWith K (f t))
    (h' : Continuous f.uncurry) (hC' : 0 ≤ C') (h_bdd : ∀ t x, ‖f t x‖ ≤ (K : ℝ) * ‖x‖ + C')
    (t₀ : ℝ) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt α (f t (α t)) (Icc (t₀ - T) (t₀ + T)) t := by
  -- Truncate the vector field outside a ball large enough that the a priori bound applies.
  set R : ℝ := max (gronwallBound ‖x₀‖ (K : ℝ) C' T) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  set g : ℝ → E → E := fun t x ↦ f t (radialTrunc R x) with hgdef
  have hglip : ∀ t, LipschitzWith (K * 2) (g t) := fun t ↦
    (h_lip t).comp (lipschitzWith_radialTrunc hR0)
  have hgcont : ∀ x, Continuous (g · x) := fun x ↦ by fun_prop
  have hgbdd : ∀ t x, ‖g t x‖ ≤ (K : ℝ) * R + C' := by
    intro t x
    calc ‖g t x‖ ≤ (K : ℝ) * ‖radialTrunc R x‖ + C' := h_bdd _ _
      _ ≤ (K : ℝ) * R + C' := by
          grw [norm_radialTrunc_le hR0]
  have hggrow : ∀ t x, ‖g t x‖ ≤ (K : ℝ) * ‖x‖ + C' := by
    intro t x
    calc ‖g t x‖ ≤ (K : ℝ) * ‖radialTrunc R x‖ + C' := h_bdd _ _
      _ ≤ (K : ℝ) * ‖x‖ + C' := by
          grw [norm_radialTrunc_le_self hR0]
  obtain ⟨α, hα0, hα⟩ := exists_solution_Icc hglip hgcont hgbdd t₀ x₀ T hT
  have hbound := norm_le_gronwallBound_of_linear_growth (f := g) K.coe_nonneg hC' hggrow hT hα
  refine ⟨α, hα0, fun t ht ↦ ?_⟩
  have h1 : ‖α t‖ ≤ R := by
    have h2 := hbound t ht
    rw [hα0] at h2
    grind
  have h3 : g t (α t) = f t (α t) := by
    simp [hgdef, radialTrunc_eq_self h1]
  rw [← h3]
  exact hα t ht

/-- Global existence of a flow for a globally Lipschitz, jointly continuous vector field of
linear growth. -/
public theorem global_existence (h_lip : ∀ t, LipschitzWith K (f t))
    (ht_bdd : ∀ t, ‖f t 0‖ ≤ C') (h' : Continuous f.uncurry) :
    ∃ Φ : ℝ → E → ℝ → E, ∀ t₀ x₀, IsIntegralCurve (Φ t₀ x₀) f ∧ Φ t₀ x₀ t₀ = x₀ := by
  -- Being `K`-Lipschitz, `f t` grows at most like `K * ‖x‖ + ‖f t 0‖`, and `‖f t 0‖ ≤ C'`.
  have hC' : 0 ≤ C' := by
    have := ht_bdd 0
    simpa using (norm_nonneg _).trans this
  have hgrow : ∀ t x, ‖f t x‖ ≤ (K : ℝ) * ‖x‖ + C' := by
    intro t x
    have h0 : ‖f t 0‖ ≤ C' := by simpa using ht_bdd t
    have hK : ‖f t x - f t 0‖ ≤ (K : ℝ) * ‖x‖ := by
      have := (h_lip t).dist_le_mul x 0
      simpa [dist_eq_norm] using this
    calc ‖f t x‖ = ‖(f t x - f t 0) + f t 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖f t x - f t 0‖ + ‖f t 0‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖x‖ + C' := by linarith
  exact exists_global_of_exists_solution_Icc h_lip
    (exists_solution_Icc_of_linear_growth h_lip h' hC' hgrow)

proof_wanted exists_nonAutonomousFlow (h_lip : ∀ t, LipschitzWith K (f t))
    (ht_bdd : ∀ t, ‖f t 0‖ ≤ C') (h' : Continuous f.uncurry) :
    ∃ Φ : NonautonomousFlow ℝ E, ∀ t₀ x₀, IsIntegralCurve (Φ t₀ x₀) f
  /-obtain ⟨Φ, hΦ⟩ := global_existence h_lip ht_bdd h'
  have : ∀ (t₀ t₁ t₂ : ℝ) (x : E), Φ t₀ (Φ t₁ x t₂) t₁ = Φ t₀ x t₂ := by
    intro t₀ t₁ t₂ x
    set γ₁ := fun t₂ ↦ Φ t₀ (Φ t₁ x t₂) t₁ with hγ₁
    set γ₂ := Φ t₀ x with hγ₂
    suffices γ₁ = γ₂ by grind
    have hγ₁_int : IsIntegralCurve γ₁ f := by
      simp [hγ₁]
      sorry
    have hγ₂_int : IsIntegralCurve γ₂ f := by
      sorry
    have ht₀ : γ₁ t₀ = γ₂ t₀ := by
      sorry
    have h_lip : ∀ t : ℝ, LipschitzOnWith K (f t) Set.univ := by simpa
    exact hγ₁_int.eq h_lip (by simp) hγ₂_int (by simp) ht₀
  use ⟨Φ, (hΦ · · |>.2), this⟩
  simpa using (hΦ · · |>.1)-/

attribute [fun_prop] LipschitzWith.continuous

/-- A time-independent globally Lipschitz continuous vector field admits a global fundamental
solution. -/
public theorem global_existence_autonomous {f : E → E} (h_lip : LipschitzWith K f) :
    ∃ Φ : ℝ → E → ℝ → E, ∀ t₀ x₀, IsIntegralCurve (Φ t₀ x₀) (fun _ ↦ f) ∧ Φ t₀ x₀ t₀ = x₀ :=
  global_existence (fun _ ↦ h_lip) (fun _ ↦ le_refl _) (by fun_prop)

public theorem LipschitzWith.exists_autonomousFlow {f : E → E} (h_lip : LipschitzWith K f) :
    ∃ Φ : AutonomousFlow ℝ E, ∀ x₀, IsIntegralCurve (Φ · x₀) (fun _ ↦ f) := by
  obtain ⟨Φ, hΦ⟩ := global_existence_autonomous h_lip
  have : ∀ x, IsIntegralCurve (Φ 0 x) (fun _ ↦ f) := (hΦ 0 · |>.1)
  suffices ∀ (t t' : ℝ) (x : E), Φ 0 (Φ 0 x t') t = Φ 0 x (t + t') by
    use ⟨fun t x ↦ Φ 0 x t, (hΦ 0 · |>.2), this⟩
  intro t t' x
  set γ₁ := fun t ↦ Φ 0 (Φ 0 x t') t with hγ₁
  set γ₂ := fun t ↦ Φ 0 x (t + t') with hγ₂
  suffices γ₁ = γ₂ by grind
  have hγ₁_int : IsIntegralCurve γ₁ (fun _ ↦ f) :=
    (hΦ 0 (Φ 0 x t')).1
  have hγ₂_int : IsIntegralCurve γ₂ (fun _ ↦ f) :=
    (hΦ 0 x).1.comp_add t'
  have ht₀ : γ₁ 0 = γ₂ 0 := by simp [hγ₁, hγ₂, hΦ]
  have h_lip : ∀ t : ℝ, LipschitzOnWith K f Set.univ := by simpa
  exact hγ₁_int.eq h_lip (by simp) hγ₂_int (by simp) ht₀

attribute [fun_prop] LipschitzOnWith LipschitzWith.lipschitzOnWith

omit [CompleteSpace E] in
public theorem LipschitzWith.unique_autonomousFlow {f : E → E} (h_lip : LipschitzWith K f)
    {Φ₁ Φ₂ : AutonomousFlow ℝ E} (hΦ₁ : ∀ x₀, IsIntegralCurve (Φ₁ · x₀) (fun _ ↦ f))
    (hΦ₂ : ∀ x₀, IsIntegralCurve (Φ₂ · x₀) (fun _ ↦ f)) : Φ₁ = Φ₂ := by
  ext t x
  suffices (Φ₁ · x) = (Φ₂ · x) by
    rw [funext_iff] at this
    grind
  have h_lip : LipschitzOnWith K f univ := by fun_prop
  have h₀ : Φ₁ 0 x = Φ₂ 0 x := by simp
  exact (hΦ₁ x).eq (fun _ ↦ h_lip) (by simp) (hΦ₂ x) (by simp) h₀

end GlobalExistence

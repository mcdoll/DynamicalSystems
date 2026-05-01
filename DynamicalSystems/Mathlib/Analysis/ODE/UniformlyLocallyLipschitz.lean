/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique

/-! # Uniform locally Lipschitz functions

In this file, we prove that an ODE `d/dt x = f(t, x)` admits a global fundamental solution
if `f` satisfies `‖f t x‖ ≤ a t + b t * ‖x‖` for locally integrable `a` and `b`.
-/


@[expose] public noncomputable section

open scoped NNReal Filter Topology

variable {E E' F : Type*}

variable [NormedAddCommGroup E] --[NormedSpace ℝ E]

variable {f : ℝ → E → E} {s : Set (ℝ × E)}

/-- A function is uniformly locally Lipschitz if for every `t₀` and `x₀` there exists a `K` such
that `f t` is Lipschitz on a neighbourhood of `x₀` for all `t` in a neighborhood of `t₀`.

The main use of this definition is that it gives a sufficent condition for local existence of
ODEs using the Picard-Lindelöf theorem. -/
@[fun_prop]
def UniformlyLocallyLipschitzOn (f : ℝ → E → E) (s : Set (ℝ × E)) : Prop :=
  ∀ ⦃t₀ x₀⦄, (t₀, x₀) ∈ s → ∃ K, ∃ s' ∈ 𝓝[((t₀, ·)) ⁻¹' s] x₀, ∀ᶠ t in 𝓝 t₀,
    LipschitzOnWith K (f t) (s' ∩ ((t, ·)) ⁻¹' s)

/-- A function is uniformly locally Lipschitz if for every `t₀` and `x₀` there exists a `K` such
that `f t` is Lipschitz on a neighbourhood of `x₀` for all `t` in a neighborhood of `t₀`.

The main use of this definition is that it gives a sufficent condition for local existence of
ODEs using the Picard-Lindelöf theorem. -/
@[fun_prop]
def UniformlyLocallyLipschitz (f : ℝ → E → E) : Prop :=
  ∀ (t₀ : ℝ) (x₀ : E), ∃ (K : ℝ≥0), ∃ s ∈ 𝓝 x₀, ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (f t) s

@[fun_prop]
theorem ContDiff.uniformlyLocallyLipschitz [NormedSpace ℝ E] {f : ℝ → E → E}
    (hf' : ContDiff ℝ 1 f.uncurry) : UniformlyLocallyLipschitz f := by
  intro t₀ x₀
  obtain ⟨K, s, hs, h⟩ := hf'.locallyLipschitz ⟨t₀, x₀⟩
  use K
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hs⟩ := hs
  rw [← ball_prod_same] at hs
  use Metric.ball x₀ ε, Metric.ball_mem_nhds x₀ hε
  rw [eventually_nhds_iff ]
  use Metric.ball t₀ ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε
  intro t ht x hx y hy
  convert h.mono hs (Set.mk_mem_prod ht hx) (Set.mk_mem_prod ht hy)
  rw [Prod.edist_eq]
  simp

namespace UniformlyLocallyLipschitzOn

variable {s s' : Set (ℝ × E)}

theorem univ (hf : UniformlyLocallyLipschitzOn f Set.univ) : UniformlyLocallyLipschitz f := by
  intro t₀ x₀
  obtain ⟨K, s', hs', h⟩ := hf (Set.mem_univ (t₀, x₀))
  simp only [Set.preimage_univ, nhdsWithin_univ, Set.inter_univ] at hs' h
  use K, s', hs'

theorem mono (hf : UniformlyLocallyLipschitzOn f s) (hs : s' ⊆ s) :
    UniformlyLocallyLipschitzOn f s' := by
  intro t₀ x₀ htx
  obtain ⟨K, t, ht, h⟩ := hf (hs htx)
  have : t ∈ 𝓝[(fun x ↦ (t₀, x)) ⁻¹' s'] x₀ := by
    apply nhdsWithin_mono _ _ ht
    grw [hs]
  use K, t, this
  filter_upwards [h] with x h
  apply h.mono
  simp only [Set.subset_inter_iff, Set.inter_subset_left, true_and]
  intro y hy
  exact hs hy.2

@[fun_prop]
theorem _root_.LocallyLipschitzOn.uniformlyLocallyLipschitzOn {f : E → E} {s : Set E}
    (hf : LocallyLipschitzOn s f) :
    UniformlyLocallyLipschitzOn (fun _ : ℝ ↦ f) (Set.univ ×ˢ s) := by
  intro t₀ x₀ ⟨_, (hx₀ : x₀ ∈ s)⟩
  obtain ⟨K, s', hs', h⟩ := hf hx₀
  use K, s'
  simpa [hs'] using h.mono Set.inter_subset_left

end UniformlyLocallyLipschitzOn

namespace UniformlyLocallyLipschitz

theorem uniformlyLocallyLipschitzOn (hf : UniformlyLocallyLipschitz f) (s : Set (ℝ × E)) :
    UniformlyLocallyLipschitzOn f s := by
  intro t₀ x₀ _htx
  obtain ⟨K, s', hs', h⟩ := hf t₀ x₀
  use K, s', mem_nhdsWithin_of_mem_nhds hs'
  filter_upwards [h] with x h
  exact h.mono Set.inter_subset_left

@[fun_prop]
theorem add {f g : ℝ → E → E} (hf : UniformlyLocallyLipschitz f)
    (hg : UniformlyLocallyLipschitz g) : UniformlyLocallyLipschitz (f + g) := by
  intro t₀ x₀
  obtain ⟨K₁, s₁, hs₁, h₁⟩ := hf t₀ x₀
  obtain ⟨K₂, s₂, hs₂, h₂⟩ := hg t₀ x₀
  use K₁ + K₂, s₁ ∩ s₂, Filter.inter_mem hs₁ hs₂
  filter_upwards [h₁.and h₂] with x ⟨h₁, h₂⟩
  exact (h₁.mono Set.inter_subset_left).add (h₂.mono Set.inter_subset_right)

@[fun_prop]
theorem _root_.LocallyLipschitz.uniformlyLocallyLipschitz {f : E → E} (hf : LocallyLipschitz f) :
    UniformlyLocallyLipschitz (fun _ : ℝ ↦ f) := by
  intro t₀ x₀
  obtain ⟨K, s, hs, h⟩ := hf x₀
  use K, s, hs
  exact Filter.eventually_const.mpr h

@[simp]
theorem const (f : ℝ → E) : UniformlyLocallyLipschitz (fun t _ ↦ f t) := by
  intro t₀ x₀
  use 0, Set.univ
  simp

end UniformlyLocallyLipschitz

variable {s : Set (ℝ × E)}

open Metric

/-- If `f` is continuous and uniformly locally Lipschitz, then the ODE `d/dt x = f t x` has a local
solution for every initial condition `x t₀ = x₀`. -/
theorem UniformlyLocallyLipschitzOn.isPicardLindelof (hf : UniformlyLocallyLipschitzOn f s)
    (hf' : ∀ x, ContinuousOn (f · x) ((·, x) ⁻¹' s))
    {t₀ : ℝ} {x₀ : E} (hs : s ∈ 𝓝 (t₀, x₀)) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < a) (_ : 0 < r),
    IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [hε.le])⟩ x₀ a r L K := by
  obtain ⟨K, s', hs', h⟩ := hf <| mem_of_mem_nhds hs
  have hst₀ : ((t₀, ·)) ⁻¹' s ∈ 𝓝 x₀ := by
    rw [mem_nhds_prod_iff] at hs
    obtain ⟨u, hu, v, hv, huv⟩ := hs
    rw [Set.prod_subset_iff] at huv
    specialize huv t₀ (mem_of_mem_nhds hu)
    apply Filter.mem_of_superset hv
    simpa using huv
  have h' : {t | LipschitzOnWith K (f t) (s' ∩ ((t, ·)) ⁻¹' s) } ×ˢ s' ∈ 𝓝 (t₀, x₀) := by
    apply prod_mem_nhds h (nhds_of_nhdsWithin_of_nhds hst₀ hs')
  have h_nhds :=
    (Metric.nhds_basis_closedBall (x := t₀)).prod_nhds (Metric.nhds_basis_closedBall (x := x₀))
  obtain ⟨⟨ε, a⟩, ⟨(hε : 0 < ε), (ha : 0 < a)⟩, hεa⟩ := h_nhds.mem_iff.mp (Filter.inter_mem hs h')
  simp only [Set.subset_inter_iff, Set.prod_subset_prod_iff, Metric.closedBall_eq_empty] at hεa
  have h : ∀ t ∈ Metric.closedBall t₀ ε, LipschitzOnWith K (f t) (s' ∩ ((t, ·)) ⁻¹' s) := by grind
  have ha' : Metric.closedBall x₀ a ⊆ s' := by grind
  have hxst : ∀ {t x} (ht : t ∈ Metric.closedBall t₀ ε) (hx : x ∈ Metric.closedBall x₀ a),
      (t, x) ∈ s := by
    intro t x ht hx
    have := hεa.1 (Set.mk_mem_prod ht hx)
    simpa using this
  have h_cont : ∀ x ∈ Metric.closedBall x₀ a, ContinuousOn (f · x) (closedBall t₀ ε) := by
    intro x hx
    apply (hf' x).mono
    intro t ht
    simpa using hxst ht hx
  obtain ⟨C, hC⟩ := (isCompact_closedBall t₀ ε).exists_bound_of_continuousOn
    (h_cont x₀ <| mem_closedBall_self ha.le)
  have hC' : 0 ≤ C := by
    grw [← hC t₀ (Metric.mem_closedBall_self hε.le)]
    positivity
  set L := K * a + C + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (t : ℝ) (ht : t ∈ Metric.closedBall t₀ ε) (x : E) (hx : x ∈ Metric.closedBall x₀ a) :
      ‖f t x‖ ≤ L := by
    rw [hL]
    calc
      ‖f t x‖ ≤ ‖f t x - f t x₀‖ + ‖f t x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f t x₀‖ := by
        gcongr
        have hx₀' := Metric.mem_closedBall_self (x := x₀) ha.le
        exact (h t ht).norm_sub_le ⟨ha' hx, hxst ht hx⟩ ⟨ha' hx₀', hxst ht hx₀'⟩
      _ ≤ K * a + ‖f t x₀‖ := by
        gcongr
        rwa [← mem_closedBall_iff_norm]
      _ ≤ L := by
        rw [hL]
        grw [hC t ht]
        simp
  set ε' := min (ε / 2) (a / (2 * L)) with hε'
  have hε'' : ε' < ε := by
    rw [hε']
    grw [Std.min_le_left]
    simp [hε]
  use ε', by positivity, .mk a ha.le, .mk (a / 2) (by positivity), .mk L hL0.le, K,
    (NNReal.coe_pos.mp ha), (by
    simp only [← NNReal.coe_pos, NNReal.coe_mk, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    positivity)
  constructor
  · intro t ht
    rw [← Real.closedBall_eq_Icc] at ht
    have ht' : t ∈ Metric.closedBall t₀ ε := closedBall_subset_closedBall hε''.le ht
    apply (h t ht').mono (fun x hx ↦ ⟨ha' hx, ?_⟩)
    apply hxst ht' hx
  · intro x hx
    rw [← Real.closedBall_eq_Icc]
    exact (h_cont x hx).mono (closedBall_subset_closedBall hε''.le)
  · intro t ht x hx
    rw [← Real.closedBall_eq_Icc] at ht
    apply hb t (closedBall_subset_closedBall hε''.le ht) x hx
  · calc
      _ = L * min (ε / 2) (a / (2 * L)) := by simp [hε']
      _ ≤ L * (a / (2 * L)) := by grw [Std.min_le_right]
      _ = a / 2 := by field_simp
      _ = _ := by simp [field]; ring

theorem UniformlyLocallyLipschitzOn.lipschitzOnWith (hf : UniformlyLocallyLipschitzOn f s)
    (hf' : Continuous f) {t₀ : ℝ} {x₀ : E} (hs : s ∈ 𝓝 (t₀, x₀)) :
    ∃ K, ∃ ε > 0, ∃ a > 0, ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
    LipschitzOnWith K (f t) (closedBall x₀ a) := by
  obtain ⟨ε, hε, a, r, L, K, ha, hr, h⟩ := hf.isPicardLindelof (by fun_prop) hs
  use K, ε, hε, a, ha
  exact h.lipschitzOnWith

/-- If `f` is continuous and uniformly locally Lipschitz, then the ODE `d/dt x = f t x` has a local
solution for every initial condition `x t₀ = x₀`. -/
theorem UniformlyLocallyLipschitzOn.exists_forall_mem_closedBall_eq_isIntegralCurveOn
    [NormedSpace ℝ E] [CompleteSpace E]
    (hf : UniformlyLocallyLipschitzOn f s) (hf' : ∀ x, ContinuousOn (f · x) ((·, x) ⁻¹' s))
    {t₀ x₀} (hs : s ∈ 𝓝 (t₀, x₀)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (r : ℝ) (_ : 0 < r) (α : E → ℝ → E),
    ∀ x ∈ Metric.closedBall x₀ r, α x t₀ = x ∧
    IsIntegralCurveOn (α x) f (Set.Icc (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, a, r, L, K, ha, hr, h⟩ := hf.isPicardLindelof hf' hs
  use ε, hε, r.1, hr
  exact h.exists_forall_mem_closedBall_eq_isIntegralCurveOn

/-- If `f` is continuous and uniformly locally Lipschitz, then the ODE `d/dt x = f t x` has a local
solution for every initial condition `x t₀ = x₀`. -/
theorem UniformlyLocallyLipschitz.isPicardLindelof (hf : UniformlyLocallyLipschitz f)
    (hf' : Continuous f) (t₀ : ℝ) (x₀ : E) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < a) (_ : 0 < r),
    IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [hε.le])⟩ x₀ a r L K := by
  obtain ⟨ε, hε, a, r, L, K, ha, hr, h⟩ := hf.uniformlyLocallyLipschitzOn Set.univ
    |>.isPicardLindelof (t₀ := t₀) (x₀ := x₀) (by fun_prop) Filter.univ_mem
  use ε, hε, a, r, L, K

/-- If `f` is continuous and uniformly locally Lipschitz, then the ODE `d/dt x = f t x` has a local
solution for every initial condition `x t₀ = x₀`. -/
theorem UniformlyLocallyLipschitz.exists_forall_mem_closedBall_eq_isIntegralCurveOn
    [NormedSpace ℝ E] [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hf' : Continuous f) (t₀ : ℝ) (x₀ : E) :
    ∃ (ε : ℝ) (_ : 0 < ε) (r : ℝ) (_ : 0 < r) (α : E → ℝ → E),
    ∀ x ∈ Metric.closedBall x₀ r, α x t₀ = x ∧
    IsIntegralCurveOn (α x) f (Set.Icc (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, a, r, L, K, ha, hr, h⟩ := hf.isPicardLindelof hf' t₀ x₀
  use ε, hε, r.1, hr
  exact h.exists_forall_mem_closedBall_eq_isIntegralCurveOn


variable [NormedSpace ℝ E]

/-- foo -/
def IsExistenceIntervalOn (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (I : Set ℝ) (s : ℝ → Set E) : Prop :=
  t₀ ∈ I ∧ IsPreconnected I ∧ ∃ u : ℝ → E, u t₀ = x₀ ∧ IsIntegralCurveOn u f I ∧ ∀ t ∈ I, u t ∈ s t

/-- foo -/
def IsExistenceInterval (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (I : Set ℝ) : Prop :=
  t₀ ∈ I ∧ IsPreconnected I ∧ ∃ u : ℝ → E, u t₀ = x₀ ∧ IsIntegralCurveOn u f I

/-- foo -/
def maximalExistenceIntervalOn (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (s : ℝ → Set E) : Set ℝ :=
  ⋃₀ { I | IsExistenceIntervalOn f t₀ x₀ I s }

/-- foo -/
def maximalExistenceInterval (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) : Set ℝ :=
  ⋃₀ { s | IsExistenceInterval f t₀ x₀ s }

-- Todo: define the maximal existence interval
-- prove the limit property

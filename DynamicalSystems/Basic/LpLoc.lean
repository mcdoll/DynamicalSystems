/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Local `Lp` functions
- define restriction of Lp functions
- locally Lp functions

-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Bornology
open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

variable {s : Set α} {f : α →ₘ[μ] E}

section eLpNorm

@[simp]
theorem lpAddConst_top : ∞.LpAddConst = 1 := rfl

theorem eLpNorm_add_measure {f : α → E} :
    eLpNorm f p (μ + ν) ≤ p.LpAddConst * (eLpNorm f p μ + eLpNorm f p ν) := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp
  · simp only [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    simp only [ae_add_measure_iff]
    constructor
    · have : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ eLpNormEssSup f μ :=
        ENNReal.ae_le_essSup (fun y ↦ ‖f y‖ₑ)
      filter_upwards [this] with x hx
      grw [hx]
      simp
    · have : ∀ᵐ (x : α) ∂ν, ‖f x‖ₑ ≤ eLpNormEssSup f ν :=
        ENNReal.ae_le_essSup (‖f ·‖ₑ)
      filter_upwards [this] with x hx
      grw [hx]
      simp
  · rw [ENNReal.toReal_pos_iff] at hp
    simp_rw [eLpNorm_eq_eLpNorm' hp.1.ne' hp.2.ne, eLpNorm'_eq_lintegral_enorm, one_div,
      lintegral_add_measure]
    apply ENNReal.rpow_add_le_mul_rpow_add_rpow''

end eLpNorm

namespace MemLp

attribute [fun_prop] MemLp MemLp.add MemLp.sub MemLp.neg MemLp.aestronglyMeasurable

theorem add_measure {f : α → E} (hμ : MemLp f p μ) (hν : MemLp f p ν) : MemLp f p (μ + ν) := by
  constructor
  · simp only [aestronglyMeasurable_add_measure_iff]
    exact ⟨hμ.aestronglyMeasurable, hν.aestronglyMeasurable⟩
  · grw [eLpNorm_add_measure]
    rw [ENNReal.mul_lt_top_iff, ENNReal.add_lt_top]
    exact Or.inl ⟨p.LpAddConst_lt_top, ⟨hμ.2, hν.2⟩⟩

end MemLp


section MemLpLoc

/-- A function `u` is locally in `Lp` if for every bounded measurable set `s`, `u` is in `Lp` with
respect to measure `μ` restricted to `s`. -/
@[fun_prop]
def MemLpLoc [Bornology α] (u : α → E) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  ∀ s : Set α, MeasurableSet s ∧ IsBounded s → MemLp u p (μ.restrict s)

/-- A function `u` is locally in `Lp` if for every bounded measurable set `s`, `u` is in `Lp` with
respect to measure `μ` restricted to `s`. -/
@[fun_prop]
def MemLpLoc' [TopologicalSpace α] (u : α → E) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  ∀ x, ∃ s : Set α, s ∈ 𝓝 x ∧ MemLp u p (μ.restrict s)

section Topology

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
theorem MemLpLoc'.memLp_restrict_isCompact {f : α → E} [TopologicalSpace α]
    (hf : MemLpLoc' f p μ) (hs : IsCompact s) : MemLp f p (μ.restrict s) := by
  refine hs.induction_on (by simp) ?_ ?_ ?_
  · intro s t hst h
    exact h.mono_measure (μ.restrict_mono_set hst)
  · intro s t hs ht
    apply (hs.add_measure ht).mono_measure
    exact Measure.restrict_union_le s t
  · intro x hx
    obtain ⟨s', hs', hs''⟩ := hf x
    exact ⟨s', mem_nhdsWithin_of_mem_nhds hs', hs''⟩

end Topology

section Bornology

variable [Bornology α]

variable {u v : α → E}

@[fun_prop]
theorem MemLpLoc.memLp {s : Set α} (hs : MeasurableSet s) (hs' : IsBounded s)
    (hu : MemLpLoc u p μ) : MemLp u p (μ.restrict s) := hu s ⟨hs, hs'⟩

@[fun_prop]
theorem MemLpLoc.aestronglyMeasurable {s : Set α} (hs : MeasurableSet s) (hs' : IsBounded s)
    (hu : MemLpLoc u p μ) : AEStronglyMeasurable u (μ.restrict s) :=
  (hu s ⟨hs, hs'⟩).aestronglyMeasurable

theorem memLpLoc_prod_iff {u : α → E × F} :
    MemLpLoc u p μ ↔ MemLpLoc (fun x ↦ (u x).1) p μ ∧ MemLpLoc (fun x ↦ (u x).2) p μ := by
  constructor
  · intro h
    exact ⟨(h · · |>.fst), (h · · |>.snd)⟩
  · intro ⟨h₁, h₂⟩ s hs
    exact MemLp.of_fst_snd ⟨h₁ s hs, h₂ s hs⟩

theorem memLpLoc_withLp_prod_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : α → WithLp p (E × F)} :
    MemLpLoc u p μ ↔ MemLpLoc (WithLp.fst <| u ·) p μ ∧ MemLpLoc (WithLp.snd <| u ·) p μ := by
  constructor
  · intro h
    exact ⟨(h · · |>.prodLp_fst), (h · · |>.prodLp_snd)⟩
  · intro ⟨h₁, h₂⟩ s hs
    exact MemLp.of_fst_of_snd_prodLp ⟨h₁ s hs, h₂ s hs⟩

theorem memLpLoc_congr_ae (huv : u =ᵐ[μ] v) : MemLpLoc u p μ ↔ MemLpLoc v p μ := by
  congrm (∀ s hs, ?_)
  exact memLp_congr_ae huv.restrict

theorem MemLpLoc.congr_ae (hu : MemLpLoc u p μ) (huv : u =ᵐ[μ] v) : MemLpLoc v p μ :=
  (memLpLoc_congr_ae huv).mp hu

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.add (hu : MemLpLoc u p μ) (hv : MemLpLoc v p μ) : MemLpLoc (u + v) p μ := by
  intro s ⟨hs, hs'⟩
  fun_prop

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.sub (hu : MemLpLoc u p μ) (hv : MemLpLoc v p μ) : MemLpLoc (u - v) p μ := by
  intro s ⟨hs, hs'⟩
  fun_prop

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.neg (hu : MemLpLoc u p μ) : MemLpLoc (-u) p μ := by
  intro s ⟨hs, hs'⟩
  fun_prop

@[to_fun (attr := fun_prop)]
theorem memLpLoc_finsetSum {ι} (s₀ : Finset ι) {u : ι → α → E} (hu : ∀ i ∈ s₀, MemLpLoc (u i) p μ) :
    MemLpLoc (∑ i ∈ s₀, u i) p μ := by
  intro s hs
  exact memLp_finsetSum' s₀ (hu · · s hs)

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E] {c : 𝕜}

@[fun_prop]
theorem MemLpLoc.const_smul (hu : MemLpLoc u p μ) : MemLpLoc (c • u) p μ := by
  intro s hs
  exact (hu s hs).const_smul c

theorem memLpLoc_iff_memLp_indicator :
    MemLpLoc u p μ ↔ ∀ s : Set α, MeasurableSet s ∧ IsBounded s → MemLp (s.indicator u) p μ := by
  congrm (∀ s, (hs : _) → ?_)
  rw [memLp_indicator_iff_restrict hs.1]

theorem MemLpLoc.memLp_indicator {s₀ : Set α} (hs₀ : MeasurableSet s₀) (hs₀' : IsBounded s₀)
    (hu : MemLpLoc u p μ) : MemLp (s₀.indicator u) p μ := by
  rw [memLpLoc_iff_memLp_indicator] at hu
  exact hu s₀ ⟨hs₀, hs₀'⟩

@[fun_prop]
theorem MemLpLoc.indicator {s₀ : Set α} (hs₀ : MeasurableSet s₀) (hu : MemLpLoc u p μ) :
    MemLpLoc (s₀.indicator u) p μ := by
  intro s hs
  exact (hu s hs).indicator hs₀

@[fun_prop]
theorem MemLp.memLpLoc (hu : MemLp u p μ) : MemLpLoc u p μ := by
  intro s _
  exact hu.restrict s

/-- In a bounded space, local `Lp` functions are in `Lp`. -/
@[simp]
theorem memLpLoc_iff_memLp [BoundedSpace α] : MemLpLoc u p μ ↔ MemLp u p μ := by
  constructor
  · intro h
    rw [← MeasureTheory.Measure.restrict_univ (μ := μ)]
    exact h Set.univ ⟨MeasurableSet.univ, BoundedSpace.bounded_univ⟩
  · apply MemLp.memLpLoc

end Bornology

section MetricSpace

variable [PseudoMetricSpace α] [ProperSpace α] [OpensMeasurableSpace α]
  [IsFiniteMeasureOnCompacts μ]

variable {u : α → E}

/-- Every continuous function is locally `Lp` -/
@[fun_prop]
theorem Continuous.memLpLoc (h : Continuous u) : MemLpLoc u p μ := by
  intro s ⟨hs₁, hs₂⟩
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [h.aestronglyMeasurable]
  · obtain ⟨C, hC⟩ := hs₂.isCompact_closure.exists_bound_of_continuousOn (f := u) (by fun_prop)
    apply memLp_top_of_bound (by fun_prop) C (ae_restrict_of_forall_mem hs₁ ?_)
    intro x hx
    exact hC _ (subset_closure hx)
  · rw [ENNReal.toReal_pos_iff] at hp
    rw [← MeasureTheory.integrable_norm_rpow_iff (by fun_prop) hp.1.ne' hp.2.ne,
      ← MeasureTheory.IntegrableOn]
    apply ContinuousOn.integrableOn_of_subset_isCompact (K := closure s)
    · apply Continuous.continuousOn
      apply Continuous.rpow_const (by fun_prop)
      intro; right; positivity
    · apply hs₂.isCompact_closure
    · exact hs₁
    · exact subset_closure
    · rw [← lt_top_iff_ne_top]
      exact IsBounded.measure_lt_top hs₂

end MetricSpace

end MemLpLoc

variable [Bornology α]

variable (E p) in
/-- The space of locally Lp functions. -/
def LpLoc (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | MemLpLoc f p μ }
  zero_mem' := by
    refine MemLp.memLpLoc ?_
    rw [← Lp.mem_Lp_iff_memLp]
    simp
  add_mem' {f g} hf hg :=
    (hf.add hg).congr_ae (AEEqFun.coeFn_add f g).symm
  neg_mem' {f} hf :=
    hf.neg.congr_ae (AEEqFun.coeFn_neg f).symm


end MeasureTheory

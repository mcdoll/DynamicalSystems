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

variable {α 𝕜 𝕜' ε ε' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

variable {s : Set α}

section eLpNorm

@[simp]
theorem lpAddConst_top : ∞.LpAddConst = 1 := rfl

variable [ENorm ε]

theorem eLpNorm_add_measure {f : α → ε} :
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

variable [TopologicalSpace ε] [TopologicalSpace.PseudoMetrizableSpace ε] [ENorm ε]

theorem add_measure {f : α → ε} (hμ : MemLp f p μ) (hν : MemLp f p ν) : MemLp f p (μ + ν) := by
  constructor
  · simp only [aestronglyMeasurable_add_measure_iff]
    exact ⟨hμ.aestronglyMeasurable, hν.aestronglyMeasurable⟩
  · grw [eLpNorm_add_measure]
    rw [ENNReal.mul_lt_top_iff, ENNReal.add_lt_top]
    exact Or.inl ⟨p.LpAddConst_lt_top, ⟨hμ.2, hν.2⟩⟩

end MemLp

variable [TopologicalSpace ε]

section MemLpLoc

/-- A function `u` is locally in `Lp` if for every bounded measurable set `s`, `u` is in `Lp` with
respect to measure `μ` restricted to `s`. -/
@[fun_prop]
def MemLpLoc [ENorm ε] [TopologicalSpace α] (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  ∀ x, ∀ᶠ s in (𝓝 x).smallSets, MemLp f p (μ.restrict s)

section ENorm

variable [TopologicalSpace α] [ENorm ε] {f g : α → ε}

theorem memLpLoc_prod_iff {f : α → E × F} :
    MemLpLoc f p μ ↔ MemLpLoc (fun x ↦ (f x).1) p μ ∧ MemLpLoc (fun x ↦ (f x).2) p μ := by
  simp_rw [MemLpLoc, ← forall_and, ← eventually_and]
  congrm (∀ x, ∀ᶠ s in (𝓝 x).smallSets, ?_)
  exact memLp_prod_iff

theorem memLpLoc_withLp_prod_iff [Fact (1 ≤ p)] {f : α → WithLp p (E × F)} :
    MemLpLoc f p μ ↔ MemLpLoc (WithLp.fst <| f ·) p μ ∧ MemLpLoc (WithLp.snd <| f ·) p μ := by
  simp_rw [MemLpLoc, ← forall_and, ← eventually_and]
  congrm (∀ x, ∀ᶠ s in (𝓝 x).smallSets, ?_)
  exact memLp_prodLp_iff

theorem memLpLoc_congr_ae (huv : f =ᵐ[μ] g) : MemLpLoc f p μ ↔ MemLpLoc g p μ := by
  congrm (∀ x, ∀ᶠ s in (𝓝 x).smallSets, ?_)
  exact memLp_congr_ae huv.restrict

theorem MemLpLoc.congr_ae (hu : MemLpLoc f p μ) (huv : f =ᵐ[μ] g) : MemLpLoc g p μ :=
  (memLpLoc_congr_ae huv).mp hu

@[fun_prop]
theorem MemLpLoc.indicator [TopologicalSpace ε'] [ESeminormedAddMonoid ε'] (hs : MeasurableSet s)
    {f : α → ε'} (hf : MemLpLoc f p μ) :
    MemLpLoc (s.indicator f) p μ := by
  intro x
  filter_upwards [hf x] with s' hf
  exact hf.indicator hs

end ENorm

section ContinuousENorm

variable [TopologicalSpace α] [ContinuousENorm ε] {f g : α → ε}

theorem MemLp.memLpLoc (hf : MemLp f p μ) : MemLpLoc f p μ := by
  intro x
  refine eventually_smallSets.mpr ?_
  use Set.univ
  simp only [univ_mem, Set.subset_univ, forall_const, true_and]
  intro s
  apply hf.restrict

theorem memLpLoc_iff {f : α → ε} : MemLpLoc f p μ ↔
    ∀ x, ∃ s : Set α, s ∈ 𝓝 x ∧ MemLp f p (μ.restrict s) := by
    congrm (∀ x, ?_)
    rw [eventually_smallSets']
    intro s t hst hf
    exact hf.mono_measure (μ.restrict_mono_set hst)

variable [TopologicalSpace.PseudoMetrizableSpace ε]

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
theorem MemLpLoc.memLp_restrict_isCompact (hf : MemLpLoc f p μ) (hs : IsCompact s) :
    MemLp f p (μ.restrict s) := by
  refine hs.induction_on ?_ ?_ ?_ ?_
  · simp [μ.restrict_empty]
  · intro s t hst h
    exact h.mono_measure (μ.restrict_mono_set hst)
  · intro s t hs ht
    apply (hs.add_measure ht).mono_measure
    exact Measure.restrict_union_le s t
  · intro x hx
    rw [memLpLoc_iff] at hf
    obtain ⟨s', hs', hs''⟩ := hf x
    exact ⟨s', mem_nhdsWithin_of_mem_nhds hs', hs''⟩

theorem memLpLoc_iff_memLp_isCompact [WeaklyLocallyCompactSpace α] :
    MemLpLoc f p μ ↔ ∀ s (_hs : IsCompact s), MemLp f p (μ.restrict s) := by
  constructor
  · intro h s hs
    exact h.memLp_restrict_isCompact hs
  · rw [memLpLoc_iff]
    intro h x
    obtain ⟨s, hs₁, hs₂⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds x
    use s, hs₂
    exact h s hs₁

theorem memLpLoc_iff_memLp_indicator [WeaklyLocallyCompactSpace α] [TopologicalSpace ε']
    [TopologicalSpace.PseudoMetrizableSpace ε'] [ESeminormedAddMonoid ε']
    [OpensMeasurableSpace α] [T2Space α]
    {f : α → ε'} :
    MemLpLoc f p μ ↔ ∀ s (_hs : IsCompact s), MemLp (s.indicator f) p μ := by
  rw [memLpLoc_iff_memLp_isCompact]
  congrm (∀ s hs, ?_)
  refine Iff.symm (memLp_indicator_iff_restrict ?_)
  apply hs.measurableSet

theorem MemLpLoc.memLp_indicator [OpensMeasurableSpace α] [T2Space α]
    [TopologicalSpace ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] [ESeminormedAddMonoid ε']
    {f : α → ε'} (hf : MemLpLoc f p μ) (hs : IsCompact s) :
    MemLp (s.indicator f) p μ := by
  rw [memLp_indicator_iff_restrict hs.measurableSet]
  exact hf.memLp_restrict_isCompact hs

@[fun_prop]
theorem MemLpLoc.aestronglyMeasurable (hs : IsCompact s) (hf : MemLpLoc f p μ) :
    AEStronglyMeasurable f (μ.restrict s) :=
  (hf.memLp_restrict_isCompact hs).aestronglyMeasurable

end ContinuousENorm

variable [TopologicalSpace α] {f g : α → E}

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.add (hf : MemLpLoc f p μ) (hg : MemLpLoc g p μ) : MemLpLoc (f + g) p μ := by
  intro x
  filter_upwards [hf x, hg x] with x hf hg
  exact hf.add hg

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.sub (hf : MemLpLoc f p μ) (hg : MemLpLoc g p μ) : MemLpLoc (f - g) p μ := by
  intro x
  filter_upwards [hf x, hg x] with x hf hg
  exact hf.sub hg

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.neg (hf : MemLpLoc f p μ) : MemLpLoc (-f) p μ := by
  intro x
  filter_upwards [hf x] with x hf
  exact hf.neg

@[to_fun (attr := fun_prop)]
theorem memLpLoc_finsetSum {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, MemLpLoc (f i) p μ) :
    MemLpLoc (∑ i ∈ s, f i) p μ := by
  intro x
  filter_upwards [(Filter.eventually_all_finset s).mpr (hf · · x)] with x hf'
  exact memLp_finsetSum' s hf'

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E] {c : 𝕜}

@[fun_prop]
theorem MemLpLoc.const_smul (hf : MemLpLoc f p μ) : MemLpLoc (c • f) p μ := by
  intro x
  filter_upwards [hf x] with x hf
  exact hf.const_smul c


section MetricSpace

variable [OpensMeasurableSpace α]
  [IsFiniteMeasureOnCompacts μ] [WeaklyLocallyCompactSpace α] [T2Space α]
  [SecondCountableTopologyEither α E]

variable {u : α → E}

/-- Every continuous function is locally `Lp` -/
@[fun_prop]
theorem Continuous.memLpLoc (h : Continuous u) : MemLpLoc u p μ := by
  rw [memLpLoc_iff_memLp_isCompact]
  intro s hs
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [h.aestronglyMeasurable]
  · obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn (f := u) (by fun_prop)
    apply memLp_top_of_bound (by fun_prop) C (ae_restrict_of_forall_mem hs.measurableSet ?_)
    intro x hx
    exact hC _ hx
  · rw [ENNReal.toReal_pos_iff] at hp
    rw [← MeasureTheory.integrable_norm_rpow_iff (by fun_prop) hp.1.ne' hp.2.ne,
      ← MeasureTheory.IntegrableOn]
    apply ContinuousOn.integrableOn_compact hs
    apply Continuous.continuousOn
    apply Continuous.rpow_const (by fun_prop)
    intro; right; positivity

end MetricSpace


end MemLpLoc

end MeasureTheory

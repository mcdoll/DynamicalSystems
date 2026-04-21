/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

/-! # The 𝓝ˢ filter in metric spaces

In this file we prove theorems about convergence to sets in metric spaces. -/

public section

variable {α β E : Type*}
  {s : Set E} {l : Filter α}

open Filter Metric
open scoped Topology

@[simp]
theorem tendsto_bot_iff {f : α → β} : Tendsto f l ⊥ ↔ l = ⊥  := by
  simp [Tendsto]

section TopologicalSpace

variable [TopologicalSpace E]

theorem tendsto_nhdsSet_of_tendsto_nhds {f : α → E} {x : E} (hx : x ∈ s) (hf : Tendsto f l (𝓝 x)) :
    Tendsto f l (𝓝ˢ s) :=
  hf.trans (nhds_le_nhdsSet hx)

end TopologicalSpace

namespace Metric

variable [PseudoMetricSpace E]

theorem tendsto_nhdsSet {f : α → E} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s) :
    Tendsto f l (𝓝ˢ s) ↔ ∀ ε > 0, ∀ᶠ x in l, infDist (f x) s < ε := by
  rw [(hasBasis_nhdsSet_thickening hs₁).tendsto_right_iff]
  congrm (∀ ε hε, ?_)
  simp [mem_thickening_iff_infDist_lt hs₂]

theorem mem_nhdsSet_iff {t : Set E} (hs : IsCompact s) :
    t ∈ 𝓝ˢ s ↔ ∃ ε > 0, Metric.thickening ε s ⊆ t := by
  rw [(hasBasis_nhdsSet_thickening hs).mem_iff]

end Metric

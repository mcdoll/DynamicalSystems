/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Compactness.Compact

@[expose] public section

variable {ι α E : Type*}

section TopologicalSpace

variable {ι E : Type*} [TopologicalSpace E]

/-- The limit set is the collection of all cluster points. -/
def Filter.limitSet (l : Filter ι) (g : ι → E) : Set E :=
  { p | MapClusterPt p l g }

open Filter

variable {l : Filter ι} {f : ι → E}

@[simp]
theorem mem_limitSet_iff {x : E} : x ∈ l.limitSet f ↔ MapClusterPt x l f := by rfl

theorem limitSet_subset_of_eventually {s : Set E} (hs : IsClosed s) (h : ∀ᶠ x in l, f x ∈ s) :
    l.limitSet f ⊆ s := by
  intro y hy
  exact hs.mem_of_mapClusterPt hy h

open scoped Topology

theorem IsCompact.tendsto_of_limitSet_inter_subset_singleton {s : Set E} (hs : IsCompact s) {x₀ : E}
    (hf : ∀ᶠ x in l, f x ∈ s) (h : l.limitSet f ∩ s ⊆ {x₀}) : Tendsto f l (𝓝 x₀) := by
  apply hs.tendsto_nhds_of_unique_mapClusterPt hf
  intro x hx hx'
  apply h
  rw [Set.mem_inter_iff, mem_limitSet_iff]
  exact ⟨hx', hx⟩

theorem isClosed_limitSet : IsClosed (l.limitSet f) :=
  isClosed_setOf_clusterPt

end TopologicalSpace

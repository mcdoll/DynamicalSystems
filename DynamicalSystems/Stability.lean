/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Order.Filter.Bases.Basic


/-!
# Stability
-/


@[expose] public section

variable {ι E : Type*}

namespace Filter

variable {l : Filter E} {Φ : ι → E → E} {I : Set ι}

variable (Φ l I) in
/-- A filter is stable if for every `s ∈ l` there exists a `s' ∈ l` such that for all `x ∈ s'` the
flow of `x` is contained in `s`.

Version for arbitrary time sets `I`. Forward stability is `l.IsStableOn Φ (Set.Ici 0)`. -/
def IsStableOn : Prop :=
  ∀ s ∈ l, ∃ s' ∈ l, ∀ t ∈ I, ∀ x ∈ s', Φ t x ∈ s

theorem HasBasis.isStableOn {ι' : Sort*} {p : ι' → Prop} {s : ι' → Set E} {l : Filter E}
    (h : l.HasBasis p s) (h' : ∀ i (_hi : p i), ∃ i', p i' ∧ ∀ t ∈ I, ∀ x ∈ s i', Φ t x ∈ s i) :
    l.IsStableOn Φ I := by
  intro s' hs'
  rw [h.mem_iff] at hs'
  obtain ⟨i, hpi, hsi⟩ := hs'
  obtain ⟨i', hpi', hsi'⟩ := h' i hpi
  use s i', h.mem_of_mem hpi'
  apply (hsi <| hsi' · · · ·)

end Filter

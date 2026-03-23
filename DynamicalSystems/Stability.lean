/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution

/-!
# Stability
-/


@[expose] public section

variable {ι E : Type*}

namespace Filter

variable {f : Filter E} {Φ : ι → E → E} {I : Set ι}

variable (Φ f I) in
def IsStableOn : Prop :=
  ∀ s ∈ f, ∃ s' ∈ f, ∀ t ∈ I, ∀ x ∈ s', Φ t x ∈ s

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

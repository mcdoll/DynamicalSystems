/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Order.Filter.Bases.Basic


/-! # Stability

In this file we define stability of flows with respect to an arbitrary filter.

TODO: uniform stability, characterization for metric spaces
-/


@[expose] public section

variable {ι E : Type*}

namespace Filter

variable {l : Filter E} {Φ : ι → E → E} {I : Set ι}

variable (Φ l I) in
/-- A filter is stable if for every `s ∈ l` there exists a `s' ∈ l` such that for all `x ∈ s'` the
flow of `x` is contained in `s`.

Version for arbitrary time sets `I`. Forward stability is `l.IsStableOn Φ (Set.Ici 0)`. For
non-autonomous systems with flow `Φ : ℝ → ℝ → E → E` the forward stability becomes
`∀ t₀, l.IsStableOn (Φ t₀) (Set.Ici t₀)`. -/
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

variable {l' : Filter ι}

/-- A filter `l` is attractive with respect to a filter `l'` if `l`-eventually `t ↦ Φ t x` converges
to `l` along `l'`. The main case is that `l = 𝓝 x₀` and `l' = atTop`, then the condition becomes
that for all `x` sufficiently close to `x₀`, `t ↦ Φ t x` converges to `x₀` as `t → +∞`.

For non-autonomous systems with flow `Φ : ℝ → ℝ → E → E` the forward attractiveness becomes
`∀ t₀ ∈ Set.Ici t₀, l.IsAttractive (Φ t₀) atTop`. -/
def IsAttractive : Prop :=
  ∀ᶠ x in l, Tendsto (Φ · x) l' l

end Filter

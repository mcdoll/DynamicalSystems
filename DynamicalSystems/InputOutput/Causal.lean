/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Basic.LpLoc

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α E F : Type*}
  [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] [Bornology α]
  {f g : (α → E) → α → F} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

variable (p)
/-- A (nonlinear) operator `f` is called *causal* if it maps local `Lp` functions
to local `Lp` functions and if `(f u)_t` is equal to `(f u_t)_t` where `u_t` denotes the restriction
of `u` to `s t`.

The traditional definition of causality uses `α := ℝ≥0` and `s := Set.Ici`. -/
@[fun_prop]
structure IsCausal (f : (α → E) → α → F) (s : ι → Set α) (p : ℝ≥0∞) (μ : Measure α := by volume_tac)
    where
  memLpLoc : ∀ u, MemLpLoc u p μ → MemLpLoc (f u) p μ
  causal : ∀ t u, MemLpLoc u p μ → (s t).indicator (f <| (s t).indicator u) = (s t).indicator (f u)

theorem IsCausal.add (hf : IsCausal f s p μ) (hg : IsCausal g s p μ) : IsCausal (f + g) s p μ := by
  constructor
  · intro u hu
    have := hf.1 u hu
    have := hg.1 u hu
    simp only [Pi.add_apply]
    fun_prop
  · intro t u hu
    have hf' := hf.2 t u hu
    have hg' := hg.2 t u hu
    simp only [Pi.add_apply, indicator_add', hf', hg']

/- Todo:
- `sub`, `neg`, `const_smul`, `const` -/

/-- If `f` is causal, then two functions with the same past have the same output. -/
theorem IsCausal.eq_of_eq (hf : IsCausal f s p μ) {u v : α → E} {t : ι} (hu : MemLpLoc u p μ)
    (hv : MemLpLoc v p μ) (h : (s t).indicator u = (s t).indicator v) :
    (s t).indicator (f u) = (s t).indicator (f v) := by
  rw [← hf.2 t u hu, ← hf.2 t v hv, h]

theorem isCausal_of_eq_of_eq (h_memLpLoc : ∀ u, MemLpLoc u p μ → MemLpLoc (f u) p μ)
    (hs : ∀ t, MeasurableSet (s t))
    (h : ∀ t u v (_hu : MemLpLoc u p μ) (_hv : MemLpLoc v p μ),
      (s t).indicator u = (s t).indicator v → (s t).indicator (f u) = (s t).indicator (f v)) :
    IsCausal f s p μ := by
  refine ⟨h_memLpLoc, ?_⟩
  intro t u hu
  exact (h t u ((s t).indicator u) hu (hu.indicator (hs t)) (by symm; simp)).symm

/- Todo: Integral operator is causal if support of kernel `k(t, τ)` is in `τ ≤ t` -/

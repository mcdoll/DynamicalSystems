/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Autonomous
public import DynamicalSystems.Stability.Lyapunov

/-! # LaSalle's invariance principle

In this file we prove LaSalle's invariance principle as well as its main consequence, namely the
convergence of trajectories to a fixed point.

## Main statements

* `IsLyapunov.tendsto_of_hasDerivAt_nonpos`

-/

@[expose] public noncomputable section

open scoped NNReal Topology

variable {α E E' F : Type*}

open Filter

section TopologicalSpace

variable [TopologicalSpace E]

variable (Φ : ℝ → E → E) (y : E)

variable {Φ y}

-- Todo: mem_limitSet_iff_exists_extraction


theorem nonempty_limitSet {K : Set E} (hK : IsCompact K)
    (h : ∃ᶠ x in Filter.atTop, Φ x y ∈ K) : ∃ x ∈ K, x ∈ (atTop.limitSet (Φ · y)) := by
  apply hK.exists_mapClusterPt_of_frequently h

variable {v : E → ℝ}

/-- If `v (Φ t y)` converges to `c`, then `v x = c` for all limit points `x`. -/
theorem eq_of_tendsto {l : Filter ℝ} {c : ℝ} (h_tendsto : Tendsto (v <| Φ · y) l (𝓝 c))
    {x : E} (hx : x ∈ l.limitSet (Φ · y)) (hvx : ContinuousAt v x) : v x = c := by
  -- this is some fairly basic result about composition of limits
  rw [mem_limitSet_iff] at hx
  have : MapClusterPt (v x) l (v <| Φ · y) := hx.continuousAt_comp hvx
  rw [mapClusterPt_iff_ultrafilter] at this
  obtain ⟨U, hU, h⟩ := this
  apply tendsto_nhds_unique h (h_tendsto.mono_left hU)

end TopologicalSpace

section UniformSpace

variable [UniformSpace E] [CompleteSpace E]

variable {Φ : ℝ≥0 → E → E} {y : E}

theorem isCompact_limitSet' (hf : TotallyBounded (Set.range (Φ · y))) :
    IsCompact (atTop.limitSet (Φ · y)) := by
  apply Filter.TotallyBounded.isCompact_setOf_clusterPt
  rw [← Filter.totallyBounded_principal_iff] at hf
  apply hf.mono
  intro s hs
  simp only [Filter.mem_principal] at hs
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  use 0
  intro t ht
  apply hs
  simp

/-- If the flow is contained in a compact set, then the limit set is compact. -/
theorem isCompact_limitSet {s : Set E} (hs : IsCompact s) (hf : ∀ t, Φ t y ∈ s) :
    IsCompact (atTop.limitSet (Φ · y)) := by
  apply isCompact_limitSet'
  apply hs.totallyBounded.subset
  intro x ⟨t, (h : Φ t y = x)⟩
  rw [← h]
  exact hf t

end UniformSpace

section DynSys

variable {f : E → E} {Φ : ℝ → E → E} {y : E} (f' : E) {t₀ : ℝ}

variable {v : E → ℝ}

/-- If a function `v` is constant on an invariant set, then the derivative of `t ↦ v (Φ t x)`
vanishes for all `x ∈ s`.

This is an easy consequence of the chain rule, but with the twist that we can only calculate
one-sided derivatives. -/
theorem deriv_eq_zero {x : E} {s : Set E} (hx : x ∈ s)
    (hs : IsInvariantSetOn Φ s (Set.Ici 0)) (c : ℝ) (hsv : ∀ x ∈ s, v x = c) :
    deriv (v <| Φ · x) 0 = 0 := by
  by_cases h : DifferentiableAt ℝ (v <| Φ · x) 0
  · calc
      _ = derivWithin (v <| Φ · x) {t | 0 ≤ t} 0 :=
        -- If a function is differentiable, then it suffices to calculate a one-sided limit
        (h.derivWithin (uniqueDiffWithinAt_Ici _)).symm
      _ = derivWithin (fun (t : ℝ) ↦ c) {t | 0 ≤ t} 0 :=
        -- the function is constant for `t ≥ 0`
        derivWithin_congr (hsv _ <| hs x hx · ·) (hsv _ (hs x hx 0 (by simp)))
      _ = 0 := by
        -- a constant function has vanishing derivative
        rw [derivWithin_fun_const, Pi.zero_apply]
  · exact deriv_zero_of_not_differentiableAt h

theorem hasDerivAt_eq_zero {x : E} {s : Set E} {f' : ℝ} (hx : x ∈ s)
    (hs : IsInvariantSetOn Φ s (Set.Ici 0)) (c : ℝ) (hsv : ∀ x ∈ s, v x = c)
    (hf : HasDerivAt (v <| Φ · x) f' 0) : f' = 0 := by
  rw [← hf.deriv, deriv_eq_zero hx hs c hsv]

/-- A bounded function with negative derivative converges. -/
theorem exists_tendsto_of_deriv {f : ℝ → ℝ} {t₀ : ℝ} (hf : ∀ t ∈ Set.Ici t₀, DifferentiableAt ℝ f t)
    (hf_pos : ∃ c, ∀ t ∈ Set.Ici t₀, c ≤ f t) (hf'_neg : ∀ t ∈ Set.Ioi t₀, deriv f t ≤ 0) :
    ∃ c, Tendsto f atTop (𝓝 c) := by
  obtain ⟨c, hf_pos⟩ := hf_pos
  have : AntitoneOn f (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
    · intro t (ht : t₀ ≤ t)
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
      exact (hf t ht.le).differentiableWithinAt
    · intro t ht
      simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
      exact hf'_neg t ht
  exact this.exists_tendsto ⟨c, hf_pos⟩

/-- A bounded function with negative derivative converges. -/
theorem exists_tendsto_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf' : ∀ t ∈ Set.Ici 0, HasDerivAt f (f' t) t)
    (hf_pos : ∃ c, ∀ {t} (_ht : 0 ≤ t), c ≤ f t) (hf'_neg : ∀ t ∈ Set.Ioi 0, f' t ≤ 0) :
    ∃ c, Filter.Tendsto f Filter.atTop (𝓝 c) := by
  apply exists_tendsto_of_deriv
  · intro t ht
    apply (hf' t ht).differentiableAt
  · apply hf_pos
  · intro t (ht : 0 < t)
    rw [(hf' t ht.le).deriv]
    apply hf'_neg t ht

section TopologicalSpace

variable [TopologicalSpace E]

variable {Φ : Flow ℝ E} {s s' : Set E}

/-- The limit set is contained in the zero set of the derivative of the Lyapunov function. -/
theorem limitSet_subset
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    {c : ℝ} (hc : Tendsto (v <| Φ · y) atTop (𝓝 c))
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hs' : atTop.limitSet (Φ · y) ⊆ s) (hΦs : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    atTop.limitSet (Φ · y) ⊆ {x | f' x = 0 } := by
  intro x hx
  have hx' : x ∈ s := hs' hx
  rw [Set.mem_setOf_eq]
  apply hasDerivAt_eq_zero hx (isInvariantSet_limitSet hs' hΦs) c _ (hf' x hx')
  intro x' hx'
  apply eq_of_tendsto hc hx' (hv_diff _ (hs' hx'))

/-- The limit set is contained in the zero set of the derivative of the Lyapunov function. -/
theorem LyapunovOn.limitSet_subset (hs : IsClosed s)
    (h_lya : IsLyapunovOn v Φ s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦs : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    atTop.limitSet (Φ · y) ⊆ {x | f' x = 0 } := by
  have h_lim : atTop.limitSet (Φ · y) ⊆ s := by
      intro x hx
      apply hs.mem_of_mapClusterPt hx hΦ_mem
  obtain ⟨c, hc⟩ := h_lya.exists_tendsto_of_eventually hΦ_mem
  apply _root_.limitSet_subset (fun _ _ ↦ h_lya.cont.continuousAt) hc hf' h_lim hΦs

/-- The limit set is contained in the zero set of the derivative of the Lyapunov function. -/
theorem limitSet_subset'
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    (h_diff : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ (v <| Φ · y) t)
    (h_deriv_neg : ∀ t ∈ Set.Ioi 0, deriv (v <| Φ · y) t ≤ 0)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h_pos : ∃ c, ∀ {t : ℝ}, 0 ≤ t → c ≤ v (Φ t y))
    (hs' : atTop.limitSet (Φ · y) ⊆ s) (hΦs : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    atTop.limitSet (Φ · y) ⊆ {x | f' x = 0 } := by
  obtain ⟨c, hc⟩ := exists_tendsto_of_deriv (f := (v <| Φ · y)) h_diff h_pos h_deriv_neg
  exact limitSet_subset hv_diff hc hf' hs' hΦs

/-- The limit set is contained in the zero set of the derivative of the Lyapunov function. -/
theorem iUnion_limitSet_subset'
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    (h_diff : ∀ y ∈ s, ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ (v <| Φ · y) t)
    (h_deriv_neg : ∀ y ∈ s, ∀ t ∈ Set.Ioi 0, deriv (v <| Φ · y) t ≤ 0)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h_pos : ∀ y ∈ s, ∃ c, ∀ {t : ℝ}, 0 ≤ t → c ≤ v (Φ t y))
    (hs' : ∀ y ∈ s, atTop.limitSet (Φ · y) ⊆ s)
    (hΦs : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    ⋃ y ∈ s, atTop.limitSet (Φ · y) ⊆ {x | f' x = 0 } := by
  apply Set.iUnion₂_subset
  intro y hy
  apply limitSet_subset' hv_diff (h_diff y hy) (h_deriv_neg y hy) hf' (h_pos y hy) (hs' y hy) hΦs

-- A fixed point is contained in `⋃ y ∈ s, limitSet (Φ ·) y`.
/- Let x ∈ K such that there exists a `t` with `Φ t x ∉ {x | fderiv ℝ v x (f x) = 0 }`, then
  `x ∉ ⋃ y ∈ s, limitSet (Φ ·) y`. -/

/-- If there exists no trajectories within the zero set of the Lyapunov function, then the limit
set consists only of the fixed point. -/
theorem limitSet_subset_of_notMem (hs : IsClosed s)
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    (h_tendsto : ∃ c, Tendsto (v <| Φ · y) atTop (𝓝 c))
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    (h : ∀ x ∈ s, ¬ x ∈ s' → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    atTop.limitSet (Φ · y) ⊆ s' := by
  intro x
  contrapose
  intro (hx : ¬x ∈ s') h'
  have h_lim : atTop.limitSet (Φ · y) ⊆ s := by
      intro x hx
      apply hs.mem_of_mapClusterPt hx hΦ_mem
  have h_inv : IsInvariantSetOn Φ (atTop.limitSet (Φ · y)) (Set.Ici 0) :=
      isInvariantSet_limitSet h_lim hΦ_cont
  by_cases! hx' : x ∈ s
  · obtain ⟨t, ht, h⟩ := h x hx' hx
    have h'' : Φ t x ∈ atTop.limitSet (Φ · y) := h_inv x h' t ht
    apply h
    apply limitSet_subset hv_diff h_tendsto.choose_spec hf' h_lim hΦ_cont h''
  · apply hx'
    apply h_lim h'

/-- If there exists no trajectories within the zero set of the Lyapunov function, then the limit
set consists only of the fixed point. -/
theorem limitSet_subset_singleton (hs : IsClosed s)
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    (h_tendsto : ∃ c, Tendsto (v <| Φ · y) atTop (𝓝 c))
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    atTop.limitSet (Φ · y) ⊆ {x₀} :=
  limitSet_subset_of_notMem hs hv_diff h_tendsto hf' hΦ_cont hΦ_mem h

theorem IsLyapunovOn.limitSet_subset_notMem (hs : IsClosed s)
    (h_lya : IsLyapunovOn v Φ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    (h : ∀ x ∈ s, ¬ x ∈ s' → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    atTop.limitSet (Φ · y) ⊆ s' := by
  apply _root_.limitSet_subset_of_notMem hs (by fun_prop) _ hf' hΦ_cont hΦ_mem h
  apply h_lya.exists_tendsto_of_eventually hΦ_mem

theorem IsLyapunovOn.limitSet_subset_singleton (hs : IsClosed s)
    (h_lya : IsLyapunovOn v Φ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    atTop.limitSet (Φ · y) ⊆ {x₀} :=
  h_lya.limitSet_subset_notMem hs hf' hΦ_cont hΦ_mem h

theorem tendsto_of_limitSet_subset (hs : IsCompact s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s) (h : atTop.limitSet (Φ · y) ⊆ s') :
    Tendsto (Φ · y) atTop (𝓝ˢ s') := by
  apply hs.tendsto_of_limitSet_inter_subset hΦ_mem
  grw [Set.inter_subset_left, h]

theorem tendsto_of_limitSet_subset_singleton {x₀ : E} (hs : IsCompact s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s) (h : atTop.limitSet (Φ · y) ⊆ {x₀}) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  rw [← nhdsSet_singleton]
  exact tendsto_of_limitSet_subset hs hΦ_mem h

section T2Space

variable [T2Space E]

/-! ## LaSalle's invariance principle  -/

/-- LaSalle's invariance principle: if no trajectory is fully contained in the zero set of the
derivative of the Lyapunov function, then `Φ · y` converges to the subset.

Version for local Lyapunov functions -/
theorem IsLyapunovOn.tendsto_nhdsSet (hs : IsCompact s)
    (h_lya : IsLyapunovOn v Φ s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h : ∀ x ∈ s, ¬ x ∈ s' → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    Tendsto (Φ · y) atTop (𝓝ˢ s') := by
  apply _root_.tendsto_of_limitSet_subset hs hΦ_mem
  exact h_lya.limitSet_subset_notMem hs.isClosed hf' (by fun_prop) hΦ_mem h

/-- LaSalle's invariance principle: if no trajectory is fully contained in the zero set of the
derivative of the Lyapunov function, then `Φ · y` converges to the fixed point.

Version for local Lyapunov functions -/
theorem IsLyapunovOn.tendsto_nhds (hs : IsCompact s)
    (h_lya : IsLyapunovOn v Φ s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  rw [← nhdsSet_singleton]
  exact h_lya.tendsto_nhdsSet hs hΦ_mem hf' h

/-- LaSalle's invariance principle: if no trajectory is fully contained in the zero set of the
derivative of the Lyapunov function, then `Φ · y` converges to the subset.

Version for global Lyapunov functions -/
theorem IsLyapunov.tendsto_nhdsSet (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ)
    (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h : ∀ x ∈ s, ¬ x ∈ s' → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    Tendsto (Φ · y) atTop (𝓝ˢ s') := by
  refine (h_lya.isLyapunovOn s).tendsto_nhdsSet hs ?_ hf' h
  rw [eventually_atTop]
  use 0
  intro t ht
  apply hs'
  convert h_lya.antitone y ht
  rw [Φ.map_zero']

/-- LaSalle's invariance principle: if no trajectory is fully contained in the zero set of the
derivative of the Lyapunov function, then `Φ · y` converges to the fixed point.

Version for global Lyapunov functions -/
theorem IsLyapunov.tendsto_nhds (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ)
    (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  rw [← nhdsSet_singleton]
  exact h_lya.tendsto_nhdsSet hs hs' hf' h


/-! ## Lyapunov's theorem for strictly decreasing Lyapunov function -/

/-- If `v` is a strict Lyapunov function, then `Φ · y` converges to the subset. -/
theorem IsLyapunovOn.tendsto_nhdsSet_of_hasDerivAt_neg (hs : IsCompact s)
    (h_lya : IsLyapunovOn v Φ s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h : ∀ x ∈ s, ¬ x ∈ s' → f' x < 0) :
    Tendsto (Φ · y) atTop (𝓝ˢ s') := by
  refine h_lya.tendsto_nhdsSet hs hΦ_mem hf' ?_
  intro x hx hx'
  use 0, by positivity
  simp
  grind

/-- If `v` is a strict Lyapunov function, then `Φ · y` converges to the fixed point. -/
theorem IsLyapunovOn.tendsto_nhds_of_hasDerivAt_neg (hs : IsCompact s)
    (h_lya : IsLyapunovOn v Φ s)
    (hΦ_mem : ∀ᶠ t in atTop, Φ t y ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → f' x < 0) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  rw [← nhdsSet_singleton]
  exact h_lya.tendsto_nhdsSet_of_hasDerivAt_neg hs hΦ_mem hf' h

/-- If `v` is a strict Lyapunov function, then `Φ · y` converges to the subset. -/
theorem IsLyapunov.tendsto_nhdsSet_of_hasDerivAt_neg (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ) (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (h : ∀ x ∈ s, ¬ x ∈ s' → f' x < 0) :
    Tendsto (Φ · y) atTop (𝓝ˢ s') := by
  refine (h_lya.isLyapunovOn s).tendsto_nhdsSet_of_hasDerivAt_neg hs ?_ hf' h
  rw [eventually_atTop]
  use 0
  intro t ht
  apply hs'
  convert h_lya.antitone y ht
  rw [Φ.map_zero']

/-- If `v` is a strict Lyapunov function, then `Φ · y` converges to the fixed point. -/
theorem IsLyapunov.tendsto_nhds_of_hasDerivAt_neg (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ) (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    {x₀ : E} (h : ∀ x ∈ s, x ≠ x₀ → f' x < 0) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  rw [← nhdsSet_singleton]
  exact h_lya.tendsto_nhdsSet_of_hasDerivAt_neg hs hs' hf' h

end T2Space

/- Let x ∈ K such that there exists a `t` with `Φ t x ∉ {x | fderiv ℝ v x (f x) = 0 }`, then
  `x ∉ ⋃ y ∈ s, limitSet (Φ ·) y`. -/

/-- If there exists no trajectories within the zero set of the Lyapunov function, then the limit
set consists only of the fixed point. -/
theorem iUnion_limitSet_eq_singleton (hs : IsClosed s)
    (hv_diff : ∀ x ∈ s, ContinuousAt v x)
    (h_tendsto : ∀ y ∈ s, ∃ c, Tendsto (v <| Φ · y) atTop (𝓝 c))
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ y ∈ s, ∀ᶠ t in atTop, Φ t y ∈ s)
    {x₀ : E} (hx₀s : x₀ ∈ s) (hx₀ : ∀ t, Φ t x₀ = x₀)
    (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    ⋃ y ∈ s, atTop.limitSet (Φ · y) = {x₀} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨y, hy, h'⟩ := hx
    apply limitSet_subset_singleton hs hv_diff (h_tendsto y hy) hf' hΦ_cont (hΦ_mem y hy) h h'
  · intro x₀ rfl
    rw [Set.mem_iUnion₂]
    use x₀, hx₀s
    simp_rw [mem_limitSet_iff, hx₀]
    exact tendsto_const_nhds.mapClusterPt

theorem IsLyapunovOn.iUnion_limitSet_eq_singleton (hs : IsClosed s)
    (h_lya : IsLyapunovOn v Φ s)
    {f' : E → ℝ} (hf' : ∀ x ∈ s, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hΦ_cont : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x)
    (hΦ_mem : ∀ y ∈ s, ∀ᶠ t in atTop, Φ t y ∈ s)
    {x₀ : E} (hx₀s : x₀ ∈ s) (hx₀ : ∀ t, Φ t x₀ = x₀)
    (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | f' x = 0 }) :
    ⋃ y ∈ s, atTop.limitSet (Φ · y) = {x₀} := by
  apply _root_.iUnion_limitSet_eq_singleton hs (by fun_prop) _ hf' hΦ_cont hΦ_mem hx₀s hx₀ h
  apply (h_lya.exists_tendsto_of_eventually <| hΦ_mem · ·)


end TopologicalSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Φ : Flow ℝ E} {s : Set E} {x₀ : E}

/-- LaSalle's invariance principle: if no trajectory is fully contained in the zero set of the
derivative of the Lyapunov function, then `Φ · y` converges to the fixed point. -/
theorem IsLyapunov.tendsto_of_forall_exists_nonMem (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ) (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    (hv_diff : Differentiable ℝ v) (hΦ_diff : ∀ x ∈ s, DifferentiableAt ℝ (Φ · x) 0)
    (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, 0 ≤ t ∧ Φ t x ∉ {x | fderiv ℝ v x (deriv (Φ · x) 0) = 0 }) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  apply h_lya.tendsto_nhds hs hs' _ h
  intro x hx
  apply HasFDerivAt.comp_hasDerivAt
  · simpa using (hv_diff x).hasFDerivAt
  · exact (hΦ_diff x hx).hasDerivAt

/-- Lyapunov's theorem: if the Lyapunov function is strictly decreasing for every point `x ≠ x₀`,
then `Φ · y` converges to the fixed point `x₀`. -/
theorem IsLyapunov.tendsto_of_fderiv_neg (hs : IsCompact s)
    (h_lya : IsLyapunov v Φ) (hs' : ∀ ⦃x⦄ (_hx : v x ≤ v y), x ∈ s)
    (hv_diff : Differentiable ℝ v) (hΦ_diff : ∀ x ∈ s, DifferentiableAt ℝ (Φ · x) 0)
    (h : ∀ x ∈ s, x ≠ x₀ → fderiv ℝ v x (deriv (Φ · x) 0) < 0) :
    Tendsto (Φ · y) atTop (𝓝 x₀) := by
  apply h_lya.tendsto_nhds_of_hasDerivAt_neg hs hs' _ h
  intro x hx
  apply HasFDerivAt.comp_hasDerivAt
  · simpa using (hv_diff x).hasFDerivAt
  · exact (hΦ_diff x hx).hasDerivAt

end DynSys

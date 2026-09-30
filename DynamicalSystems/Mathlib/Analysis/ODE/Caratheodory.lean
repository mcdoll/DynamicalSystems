/-
Copyright (c) 2026 Moritz Doll, Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Igor Zubrycki
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Caratheodory existence and uniqueness theorems

This file formalizes the foundations of Carathéodory ordinary differential equations,
generalizing classical continuous vector field theory to time-dependent measurable
inputs and integrable bounds.

## References

* Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Charles University lecture notes.
* Donal O'Regan (1997), *Existence Theory for Nonlinear Ordinary Differential Equations*,
  Mathematics and Its Applications 398, Kluwer Academic Publishers / Springer.
* Paulo M. de Carvalho-Neto, Cícero L. Frota, Pedro G. P. Torelli (2025),
  *A general version of Carathéodory's existence and uniqueness theorem*,
  arXiv:2505.24516 [math.CA].
* Filip Rindler (2018), *Calculus of Variations*, Universitext, Springer (Lemma 2.4).
* Moritz Doll, Iman Shames (2026), *Foundations of Machine-Checked Control Theory in Lean*,
  arXiv:2607.19727.

## Main definitions

* `IsCaratheodory`: vector field `f : ℝ → E → E` continuous in space for almost every time,
  and strongly measurable in time for each space point.
* `IsCaratheodoryLipschitz`: Carathéodory vector field with time-dependent $L^1$ Lipschitz bound.
* `IsCaratheodorySublinear`: Carathéodory vector field with sublinear growth (Carvalho-Neto $C_1$).
* `IsCaratheodorySolutionOn`: Volterra integral solution $γ(t) = x_0 + \int_{t_0}^t f(s, γ(s)) ds$.
* `IsAEIntegralCurveOn`, `IsAEIntegralCurve`: differential formulations almost everywhere.

## Main theorems

* `IsCaratheodory.comp_stronglyMeasurable`: (Rindler Lemma 2.4 / Pražák Lemma 3) composition
  with strongly measurable curves is almost everywhere strongly measurable.
* `IsCaratheodory.comp_continuous`: composition with continuous curves is ae strongly measurable.
* `IsCaratheodory.comp_intervalIntegrable`: composition with bounded continuous curves is
  interval integrable (Carvalho-Neto Proposition 9).
* `IsCaratheodorySolutionOn.ae_hasDerivWithinAt`: integral solutions satisfy the differential
  equation almost everywhere via the Lebesgue Differentiation Theorem.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function satisfying the Caratheodory conditions on a set `s`. -/
structure IsCaratheodoryOn (f : ℝ → E → E) (s : Set ℝ × Set E) : Prop where
  /-- Continuity in space almost everywhere in time. -/
  cont : ∀ᵐ t ∂volume.restrict s.1, Continuous (f t)
  /-- Measurability in time for each point in space. -/
  meas : ∀ x ∈ s.2, AEStronglyMeasurable (f · x) (volume.restrict s.1)

/-- A function satisfying the Caratheodory conditions.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Definition 2.
- Donal O'Regan (1997), *Existence Theory for Nonlinear ODEs*, Definition 3.2.
- Carvalho-Neto, Frota, Torelli (2025), *A general version of Carathéodory theorem*, Definition 1.
- Filip Rindler (2018), *Calculus of Variations*, Lemma 2.4.
-/
structure IsCaratheodory (f : ℝ → E → E) : Prop where
  /-- Continuity in space for almost all times. -/
  cont : ∀ᵐ t, Continuous (f t)
  /-- Almost everywhere strong measurability in time for each point in space. -/
  meas : ∀ x, AEStronglyMeasurable (f · x) volume

omit [NormedSpace ℝ E] in
/-- Bridge from Borel measurability to `IsCaratheodory` in second-countable spaces. -/
theorem IsCaratheodory.of_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E → E} (hcont : ∀ᵐ t, Continuous (f t)) (hmeas : ∀ x, Measurable (f · x)) :
    IsCaratheodory f :=
  ⟨hcont, fun x ↦ (hmeas x).stronglyMeasurable.aestronglyMeasurable⟩

omit [NormedSpace ℝ E] in
/-- Composition of a simple function with a function that is measurable in time at each point. -/
theorem SimpleFunc.comp_caratheodory (f : ℝ → E → E) (hf : ∀ x, AEStronglyMeasurable (f · x) volume)
    (g : SimpleFunc ℝ E) :
    AEStronglyMeasurable (fun t ↦ f t (g t)) volume := by
  have : (fun t ↦ f t (g t)) = ∑ x ∈ g.range, (g ⁻¹' {x}).indicator (f · x) := by
    ext t
    rw [Finset.sum_apply]
    have hmem : g t ∈ g.range := SimpleFunc.mem_range_self g t
    rw [Finset.sum_eq_single (g t)]
    · simp
    · intro y _ hy
      simp [hy.symm]
    · intro hnot
      exact (hnot hmem).elim
  rw [this]
  refine Finset.aestronglyMeasurable_sum _ fun x _ ↦ ?_
  exact (hf x).indicator (g.measurableSet_fiber x)

omit [NormedSpace ℝ E] in
/-- If `f` is a Carathéodory function and `γ` is strongly measurable, then `t ↦ f t (γ t)`
is almost everywhere strongly measurable.
Reference: Filip Rindler (2018), *Calculus of Variations*, Lemma 2.4. -/
theorem IsCaratheodory.comp_stronglyMeasurable {f : ℝ → E → E}
    (hf : IsCaratheodory f) {γ : ℝ → E} (hγ : StronglyMeasurable γ) :
    AEStronglyMeasurable (fun t ↦ f t (γ t)) volume := by
  obtain ⟨gs, hgs⟩ := hγ
  have h_meas : ∀ n, AEStronglyMeasurable (fun t ↦ f t (gs n t)) volume :=
    fun n ↦ SimpleFunc.comp_caratheodory f hf.meas (gs n)
  refine aestronglyMeasurable_of_tendsto_ae atTop h_meas ?_
  filter_upwards [hf.cont] with t ht
  exact (ht.tendsto (γ t)).comp (hgs t)

omit [NormedSpace ℝ E] in
/-- If `f` is a Carathéodory function and `γ` is continuous, then `t ↦ f t (γ t)`
is almost everywhere strongly measurable. -/
theorem IsCaratheodory.comp_continuous {f : ℝ → E → E}
    (hf : IsCaratheodory f) {γ : ℝ → E} (hγ : Continuous γ) :
    AEStronglyMeasurable (fun t ↦ f t (γ t)) volume :=
  hf.comp_stronglyMeasurable hγ.stronglyMeasurable

omit [NormedSpace ℝ E] in
/-- If `f` is a Carathéodory function, `γ` is continuous, and `f t (γ t)` is bounded by an
integrable function `m` on `[a, b]`, then `t ↦ f t (γ t)` is interval integrable.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Lemma 3.
- Donal O'Regan (1997), *Existence Theory for Nonlinear ODEs*, Chapter 3.
- Carvalho-Neto et al. (2025), *A general version of Carathéodory theorem*, Proposition 9. -/
theorem IsCaratheodory.comp_intervalIntegrable {f : ℝ → E → E}
    (hf : IsCaratheodory f) {γ : ℝ → E} (hγ : Continuous γ)
    {m : ℝ → ℝ} {a b : ℝ} (hm : IntervalIntegrable m volume a b)
    (h_bdd : ∀ᵐ t ∂volume.restrict (uIoc a b), ‖f t (γ t)‖ ≤ m t) :
    IntervalIntegrable (fun t ↦ f t (γ t)) volume a b := by
  rw [intervalIntegrable_iff] at hm ⊢
  exact Integrable.mono' hm ((hf.comp_continuous hγ).restrict) h_bdd

/-- Integral formulation of a Carathéodory solution on a set `s` with initial value `x₀` at `t₀`.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Lemma 4.
- Donal O'Regan (1997), *Existence Theory for Nonlinear ODEs*, Definition 3.1.
- Carvalho-Neto, Frota, Torelli (2025), *A general version of Carathéodory theorem*, Proposition 11.
-/
def IsCaratheodorySolutionOn (γ : ℝ → E) (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, γ t = x₀ + ∫ τ in t₀..t, f τ (γ τ)

/-- An integral Carathéodory solution satisfies the initial condition `γ t₀ = x₀`. -/
theorem IsCaratheodorySolutionOn.initial {γ : ℝ → E} {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {s : Set ℝ}
    (hsol : IsCaratheodorySolutionOn γ f t₀ x₀ s) (ht₀ : t₀ ∈ s) :
    γ t₀ = x₀ := by
  simpa using hsol t₀ ht₀

/-- An integral Carathéodory solution satisfies the differential equation almost everywhere on
`uIcc a b`.
Follows from the Lebesgue Differentiation Theorem (`IntervalIntegrable.ae_hasDerivAt_integral`). -/
theorem IsCaratheodorySolutionOn.ae_hasDerivWithinAt [CompleteSpace E] {γ : ℝ → E} {f : ℝ → E → E}
    {t₀ : ℝ} {x₀ : E} {a b : ℝ}
    (hsol : IsCaratheodorySolutionOn γ f t₀ x₀ (uIcc a b))
    (ht₀ : t₀ ∈ uIcc a b)
    (hint : IntervalIntegrable (fun τ ↦ f τ (γ τ)) volume a b) :
    ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivWithinAt γ (f t (γ t)) (uIcc a b) t := by
  have h_ldt := hint.ae_hasDerivAt_integral (E := E)
  rw [ae_restrict_iff' measurableSet_uIcc]
  filter_upwards [h_ldt] with t ht ht_mem
  have ht_deriv : HasDerivWithinAt (fun x ↦ ∫ τ in t₀..x, f τ (γ τ)) (f t (γ t)) (uIcc a b) t :=
    (ht ht_mem t₀ ht₀).hasDerivWithinAt
  have ht_add := ht_deriv.const_add x₀
  refine ht_add.congr (fun s hs ↦ ?_) ?_
  · exact (hsol s hs)
  · exact (hsol t ht_mem)

/-- `IsAEIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for almost all
`t ∈ s`. -/
def IsAEIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ᵐ t ∂volume.restrict s, HasDerivWithinAt γ (v t (γ t)) s t

/-- `IsAEIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v` almost everywhere.
That is, `γ t` is tangent to `v t (γ t)` for almost all `t : ℝ`. -/
def IsAEIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ᵐ t : ℝ, HasDerivAt γ (v t (γ t)) t

/-- A global Carathéodory integral solution satisfies the differential equation almost everywhere.
Follows from the global Lebesgue Differentiation Theorem
(`LocallyIntegrable.ae_hasDerivAt_integral`). -/
theorem IsCaratheodorySolutionOn.isAEIntegralCurve [CompleteSpace E] {γ : ℝ → E} {f : ℝ → E → E}
    {t₀ : ℝ} {x₀ : E}
    (hsol : IsCaratheodorySolutionOn γ f t₀ x₀ Set.univ)
    (hint : LocallyIntegrable (fun τ ↦ f τ (γ τ)) volume) :
    IsAEIntegralCurve γ f := by
  have h_ldt := LocallyIntegrable.ae_hasDerivAt_integral hint
  filter_upwards [h_ldt] with t ht
  have ht_deriv : HasDerivAt (fun x ↦ ∫ τ in t₀..x, f τ (γ τ)) (f t (γ t)) t := ht t₀
  have ht_add := ht_deriv.const_add x₀
  refine ht_add.congr_of_eventuallyEq ?_
  filter_upwards with s
  exact hsol s trivial

/-- A Carathéodory function that is time-dependently Lipschitz in space with an L¹ bound `ℓ`.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 8.
- Donal O'Regan (1997), *Existence Theory for Nonlinear ODEs*, Theorem 3.4.
- Paulo M. de Carvalho-Neto, Cícero L. Frota, Pedro G. P. Torelli (2025),
  *A general version of Carathéodory theorem*, Theorem 2 (Condition C₂).
-/
structure IsCaratheodoryLipschitz (f : ℝ → E → E) (ℓ : ℝ → ℝ) : Prop extends IsCaratheodory f where
  /-- Time-dependent Lipschitz bound with integrable bound `ℓ`. -/
  lip : ∀ᵐ t, ∀ x y, ‖f t x - f t y‖ ≤ ℓ t * ‖x - y‖

/-- Sublinear growth condition for Carathéodory functions.
Reference: Carvalho-Neto, Frota, Torelli (2025), Theorem 2 (Condition C₁). -/
structure IsCaratheodorySublinear (f : ℝ → E → E) (C : ℝ) (γ : ℝ → ℝ) : Prop
  extends IsCaratheodory f where
  /-- Sublinear growth bound. -/
  bound : ∀ t x, ‖f t x‖ ≤ C * ‖x‖ + γ t

/-- The Picard operator for Carathéodory differential equations. -/
noncomputable def caratheodoryPicard (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (γ : ℝ → E) (t : ℝ) : E :=
  x₀ + ∫ τ in t₀..t, f τ (γ τ)

theorem caratheodoryPicard_apply (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (γ : ℝ → E) (t : ℝ) :
    caratheodoryPicard f t₀ x₀ γ t = x₀ + ∫ τ in t₀..t, f τ (γ τ) := rfl

@[simp]
theorem caratheodoryPicard_self (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (γ : ℝ → E) :
    caratheodoryPicard f t₀ x₀ γ t₀ = x₀ := by
  simp [caratheodoryPicard]

/-- Difference between two Picard iterations bounded by the integral of the Lipschitz bound.
References:
- Dalibor Pražák (2024), *Carathéodory theory of ODEs*, Theorem 8.
- Carvalho-Neto et al. (2025), *A general version of Carathéodory theorem*, Theorem 14 (Eq. 7).
-/
theorem norm_caratheodoryPicard_sub_le {f : ℝ → E → E} {ℓ : ℝ → ℝ}
    (t₀ : ℝ) (x₀ : E) (γ₁ γ₂ : ℝ → E) {t : ℝ}
    (hlip : ∀ᵐ s ∂volume.restrict (Ι t₀ t), ∀ x y, ‖f s x - f s y‖ ≤ ℓ s * ‖x - y‖)
    (h_int₁ : IntervalIntegrable (fun τ ↦ f τ (γ₁ τ)) volume t₀ t)
    (h_int₂ : IntervalIntegrable (fun τ ↦ f τ (γ₂ τ)) volume t₀ t)
    (h_bound : IntervalIntegrable (fun τ ↦ ℓ τ * ‖γ₁ τ - γ₂ τ‖) volume t₀ t) :
    ‖caratheodoryPicard f t₀ x₀ γ₁ t - caratheodoryPicard f t₀ x₀ γ₂ t‖ ≤
      |∫ s in t₀..t, ℓ s * ‖γ₁ s - γ₂ s‖| := by
  unfold caratheodoryPicard
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub h_int₁ h_int₂]
  apply intervalIntegral.norm_integral_le_abs_of_norm_le _ h_bound
  filter_upwards [hlip] with s hs
  exact hs (γ₁ s) (γ₂ s)

omit [NormedSpace ℝ E] in
/-- Restriction of interval integrability to a subinterval. -/
theorem IntervalIntegrable.subinterval {f : ℝ → E} {a b : ℝ}
    (hint : IntervalIntegrable f volume a b)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ [[a, b]]) (hs₂ : s₂ ∈ [[a, b]]) :
    IntervalIntegrable f volume s₁ s₂ :=
  hint.mono_set (uIcc_subset_uIcc hs₁ hs₂)

/-- An integral Carathéodory solution satisfies the integral equation with respect to any new
base point `t₁` in its domain of definition. -/
theorem IsCaratheodorySolutionOn.change_basePoint
    {f : ℝ → E → E} {t₀ t₁ : ℝ} {x₀ : E} {γ : ℝ → E} {s : Set ℝ}
    (hsol : IsCaratheodorySolutionOn γ f t₀ x₀ s)
    (ht₀ : t₀ ∈ s) (ht₁ : t₁ ∈ s)
    (hint : ∀ a ∈ s, ∀ b ∈ s, IntervalIntegrable (fun τ ↦ f τ (γ τ)) volume a b) :
    IsCaratheodorySolutionOn γ f t₁ (γ t₁) s := by
  intro t ht
  have h_add := intervalIntegral.integral_add_adjacent_intervals
    (hint t₀ ht₀ t₁ ht₁) (hint t₁ ht₁ t ht)
  rw [hsol t ht, hsol t₁ ht₁, add_assoc, h_add]


/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability
public import DynamicalSystems.Basic.WithLp
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Closed loops -/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α E F : Type*}

section SetRel

variable {α β : Type*}

/-- A set relation `R` is a graph of a function if for every `a` there exists a unique `b` such that
`(a, b) ∈ R`. -/
def SetRel.IsGraph (R : SetRel α β) : Prop :=
  ∀ a, ∃! b, (a, b) ∈ R

variable {f : α → β} {R : SetRel α β}

theorem SetRel.isGraph_of_graph_eq (hf : f.graph = R) : R.IsGraph := by
  intro a
  exact ⟨f a, by simp [← hf]⟩

theorem SetRel.IsGraph.eq_of_mem (hR : R.IsGraph) {a b₁ b₂} (h₁ : (a, b₁) ∈ R) (h₂ : (a, b₂) ∈ R) :
    b₁ = b₂ := ExistsUnique.unique (hR a) h₁ h₂

theorem SetRel.IsGraph.exists_graph_eq (hR : R.IsGraph) : ∃ (f : α → β), f.graph = R := by
  obtain ⟨f, hf⟩ := R.exists_graph_eq_iff.mpr hR
  use f, hf.1

end SetRel


variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable (α E F) in
/-- A closed loop defined via relations. -/
structure SetRel.closedLoop where
  /-- foo -/
  topRel : SetRel (α → E) (α → F)
  /-- bar -/
  botRel : SetRel (α → F) (α → E)

namespace SetRel.closedLoop

/-- The relation from inputs to outputs -/
protected def inputOutput (loop : SetRel.closedLoop α E F) : SetRel (α → E × F) (α → F × E) :=
  {f | (Prod.fst ∘ f.1 - Prod.snd ∘ f.2, Prod.fst ∘ f.2) ∈ loop.topRel ∧
    (Prod.snd ∘ f.1 + Prod.fst ∘ f.2, Prod.snd ∘ f.2) ∈ loop.botRel }

/-- The relation from inputs to states

This relation is given in terms of the functions `G₁, G₂` by
`u₂ - e₂ = G₁(u₁)` and `e₁ - u₁ = G₂(u₂)`
-/
protected def inputState (loop : SetRel.closedLoop α E F) : SetRel (α → E × F) (α → E × F) :=
  {f | (Prod.fst ∘ f.2, Prod.snd ∘ f.2 - Prod.snd ∘ f.1) ∈ loop.topRel ∧
    (Prod.snd ∘ f.2, Prod.fst ∘ f.1 - Prod.fst ∘ f.2) ∈ loop.botRel }

/-- The relation from inputs to states

This relation is given in terms of the functions `G₁, G₂` by
`u₂ - e₂ = G₁(u₁)` and `e₁ - u₁ = G₂(u₂)`
-/
protected def inputStateLp (loop : SetRel.closedLoop α E F) (p : ℝ≥0∞) :
    SetRel (α → WithLp p (E × F)) (α → WithLp p (E × F)) :=
  {f | (WithLp.fst ∘ f.2, WithLp.snd ∘ f.2 - WithLp.snd ∘ f.1) ∈ loop.topRel ∧
    (WithLp.snd ∘ f.2, WithLp.fst ∘ f.1 - WithLp.fst ∘ f.2) ∈ loop.botRel }

variable {p : ℝ≥0∞} {loop : SetRel.closedLoop α E F}
variable {e : α → E × F} {u : α → E × F} {y : α → F × E} {y₁ : α → F} {y₂ : α → E}

theorem mem_inputOutput : (e, y) ∈ loop.inputOutput ↔
    (Prod.fst ∘ e - Prod.snd ∘ y, Prod.fst ∘ y) ∈ loop.topRel ∧
    (Prod.snd ∘ e + Prod.fst ∘ y, Prod.snd ∘ y) ∈ loop.botRel := by rfl

theorem mem_inputState : (e, u) ∈ loop.inputState ↔
    (Prod.fst ∘ u, Prod.snd ∘ u - Prod.snd ∘ e) ∈ loop.topRel ∧
    (Prod.snd ∘ u, Prod.fst ∘ e - Prod.fst ∘ u) ∈ loop.botRel := by rfl

theorem mem_inputState_of_mem_inputOutput (h : (e, y) ∈ loop.inputOutput) :
    (e, e - (fun x ↦ (x.2, -x.1)) ∘ y) ∈ loop.inputState := by
  constructor
  · convert h.1 using 2
    all_goals { ext; simp }
  · convert h.2 using 2
    all_goals { ext; simp }

theorem mem_inputOutput_of_mem_inputState (h : (e, u) ∈ loop.inputState)
    (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h_top : (Prod.fst ∘ u, Prod.fst ∘ y) ∈ loop.topRel)
    (h_bot : (Prod.snd ∘ u, Prod.snd ∘ y) ∈ loop.botRel) :
    (e, y) ∈ loop.inputOutput := by
  constructor
  · convert h_top using 2
    rw [sub_eq_iff_comm]
    exact h_botRel.eq_of_mem h.2 h_bot
  · convert h_bot using 2
    rw [← eq_sub_iff_add_eq']
    exact h_topRel.eq_of_mem h_top h.1

theorem blubb'' {G₁ : (α → E) → α → F} (hG₁ : Function.graph G₁ = loop.topRel)
    {G₂ : (α → F) → α → E} (hG₂ : Function.graph G₂ = loop.botRel)
    (h : (e, u) ∈ loop.inputState) :
    u = e - (fun x : α ↦ (G₂ (Prod.snd ∘ u) x, -G₁ (Prod.fst ∘ u) x)) := by
  simp only [mem_inputState, ← hG₂, ← hG₁, Function.mem_graph] at h
  ext x
  · simp [h.2]
  · simp [h.1]

theorem blubb₁ {G₁ : (α → E) → α → F} (hG₁ : Function.graph G₁ = loop.topRel)
    {G₂ : (α → F) → α → E} (hG₂ : Function.graph G₂ = loop.botRel)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F}
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) :
    u₁ = e₁ - G₂ u₂ := by
  have := blubb'' hG₁ hG₂ h
  ext x
  simp [funext_iff] at this
  simp [(this x).1]
  congr

theorem blubb₂ {G₁ : (α → E) → α → F} (hG₁ : Function.graph G₁ = loop.topRel)
    {G₂ : (α → F) → α → E} (hG₂ : Function.graph G₂ = loop.botRel)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F}
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) :
    u₂ = e₂ + G₁ u₁ := by
  have := blubb'' hG₁ hG₂ h
  ext x
  simp [funext_iff] at this
  simp [(this x).2]
  congr

theorem isGraph_inputOutput (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h : loop.inputState.IsGraph) : loop.inputOutput.IsGraph := by
  sorry

theorem isGraph_inputState (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h : loop.inputOutput.IsGraph) : loop.inputState.IsGraph := by
  sorry

variable [MeasurableSpace α] {μ : Measure α}

/-- If the map from inputs to outputs is `Lp` stable, then the map from inputs to states is also
`Lp` stable. -/
theorem isLpStable_inputOutput (h : loop.inputState.IsLpStable p μ) :
    loop.inputOutput.IsLpStable p μ := by
  refine ⟨fun e he y hy ↦ ?_⟩
  have := (h.memLp he _ (mem_inputState_of_mem_inputOutput hy)).sub he
  simp only [sub_sub_cancel_left] at this
  rw [memLp_prod_iff] at this ⊢
  simp only [Pi.neg_apply, Function.comp_apply, Prod.neg_mk, neg_neg] at this
  refine ⟨this.2, ?_⟩
  convert this.1.neg
  simp

/-- If the map from inputs to states is `Lp` stable, then the map from inputs to outputs is also
`Lp` stable provided that the inner relations are graphs. -/
theorem isLpStable_inputState (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h : loop.inputOutput.IsLpStable p μ) : loop.inputState.IsLpStable p μ := by
  refine ⟨fun e he u hu ↦ ?_⟩
  obtain ⟨G₁, hG₁⟩ := h_topRel.exists_graph_eq
  obtain ⟨G₂, hG₂⟩ := h_botRel.exists_graph_eq
  let y x := (G₁ (Prod.fst ∘ u) x, G₂ (Prod.snd ∘ u) x)
  have : (e, y) ∈ loop.inputOutput := by
    apply mem_inputOutput_of_mem_inputState hu h_topRel h_botRel
    · rw [← hG₁]
      ext x
      simp [y]
    · rw [← hG₂]
      ext x
      simp [y]
  have memLp' := h.memLp he y this
  rw [blubb'' hG₁ hG₂ hu]
  apply he.sub
  rw [MeasureTheory.memLp_prod_iff] at memLp' ⊢
  exact ⟨memLp'.2, memLp'.1.neg⟩


/- Todo: finite gain stabilities are equivalent -/

/- Todo: closed loop is causal -/

variable [Bornology α]
variable {s : ι → Set α} {p : ℝ≥0∞}

/-- Proposition 1.2.9 in van der Schaft -/
theorem isCausal_inputState (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h_topRel' : loop.topRel.IsCausal s p μ) (h_botRel' : loop.botRel.IsCausal s p μ)
    (h : loop.inputState.IsGraph) :
    loop.inputState.IsCausal s p μ := by
  /-
  informal proof:
  have : (G₁ uₜ)ₜ = (G₁ u)ₜ
  have : (G₂ uₜ)ₜ = (G₂ u)ₜ

  inputState has graph given by (e, u + FG u)
  Let e arbitrary, then there exists a unique u satisfying `G e = u`
  Take `eₜ`, again there exists a unique `uᵗ`, have to show that `(uᵗ)ₜ = uₜ`, because then
  `(G eₜ)ₜ = (uᵗ)ₜ = uₜ = (G e)ₜ`.

  The rest follows if we assume that the *truncated* feedback connection is well-posed:
  `(eₜ, uᵗ)` satisfies `(eₜ, uᵗ + FG uᵗ) ∈ inputState`
  We have that `(u + FG u)ₜ = (uₜ + (FG uₜ)ₜ)`
  -/
  constructor
  · intro e y hey he
    simp only [mem_inputState] at hey
    -- seems like we have to assume something here
    have := h_topRel'.memLpLoc hey.1
    sorry
  · intro t e y e' y' hey hey' he hy he' hy' hee'
    have htop := h_topRel'.causal t
    have hbot := h_botRel'.causal t
    sorry

/-- Proposition 1.2.9 in van der Schaft -/
theorem isCausal_inputOutput (h_topRel : loop.topRel.IsGraph) (h_botRel : loop.botRel.IsGraph)
    (h_topRel' : loop.topRel.IsCausal s p μ) (h_botRel' : loop.botRel.IsCausal s p μ)
    (h : loop.inputOutput.IsGraph) :
    loop.inputOutput.IsCausal s p μ := by
  constructor
  · intro e y hey he
    simp only [mem_inputOutput] at hey
    -- seems like we have to assume something here
    have := h_topRel'.memLpLoc hey.1
    sorry
  · intro t e y e' y' hey hey' he hy he' hy' hee'
    have htop := h_topRel'.causal t
    have hbot := h_botRel'.causal t
    sorry

variable {k₁ k₂ β₁ β₂ : ℝ≥0}

/-- The loop gain of a `Lp` feedback system. -/
noncomputable def loopGainLp (p : ℝ) (k₁ k₂ : ℝ≥0) : ℝ≥0 :=
  (2 ^ ((p - 1) / p) * max (1 + k₁) (1 + k₂)) / (1 - k₁ * k₂)

/-- The loop bias -/
noncomputable def loopBias (k₁ k₂ β₁ β₂ : ℝ≥0) : ℝ≥0 :=
  (β₁ + β₂ + k₁ * β₂ + k₂ * β₁) / (1 - k₁ * k₂)

theorem smallGainThm_part1₁
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel)
    (hG₂' : G₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hp : 1 ≤ p)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F} (hu₂ : MemLpLoc u₂ p μ)
    (he₁ : MemLpLoc e₁ p μ)
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) {t : ι}
    (ht : MeasurableSet (s t) ∧ IsBounded (s t)) :
    eLpNorm u₁ p (μ.restrict (s t)) ≤
      eLpNorm e₁ p (μ.restrict (s t)) + k₂ * eLpNorm u₂ p (μ.restrict (s t)) + β₂ := by
  calc
    _ = eLpNorm (e₁ - G₂ u₂) p (μ.restrict (s t)) := by
      rw [blubb₁ hG₁ hG₂ h]
    _ ≤ eLpNorm e₁ p (μ.restrict (s t)) + eLpNorm (G₂ u₂) p (μ.restrict (s t)) := by
      apply MeasureTheory.eLpNorm_sub_le
      · apply (he₁ (s t) ht).aestronglyMeasurable
      · apply (hG₂'.memLpLoc hu₂ (s t) ht).aestronglyMeasurable
      · exact hp
    _ ≤ _ := by
      rw [add_assoc]
      gcongr
      apply hG₂'.stableWith _ _ hu₂

theorem smallGainThm_part1₂
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    (hG₁' : G₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel) (hp : 1 ≤ p)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F}
    (hu₁ : MemLpLoc u₁ p μ) (he₂ : MemLpLoc e₂ p μ)
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) {t : ι}
    (ht : MeasurableSet (s t) ∧ IsBounded (s t)) :
    eLpNorm u₂ p (μ.restrict (s t)) ≤
      eLpNorm e₂ p (μ.restrict (s t)) + k₁ * eLpNorm u₁ p (μ.restrict (s t)) + β₁ := by
  calc
    _ = eLpNorm (e₂ + G₁ u₁) p (μ.restrict (s t)) := by
      rw [blubb₂ hG₁ hG₂ h]
    _ ≤ eLpNorm e₂ p (μ.restrict (s t)) + eLpNorm (G₁ u₁) p (μ.restrict (s t)) := by
      apply MeasureTheory.eLpNorm_add_le
      · apply (he₂ (s t) ht).aestronglyMeasurable
      · apply (hG₁'.memLpLoc hu₁ (s t) ht).aestronglyMeasurable
      · exact hp
    _ ≤ _ := by
      rw [add_assoc]
      gcongr
      apply hG₁'.stableWith _ _ hu₁

theorem smallGainThm_part2₁
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    (hG₁' : G₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel)
    (hG₂' : G₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hp : 1 ≤ p) (hk : k₁ * k₂ < 1)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F}
    (hu₁ : MemLpLoc u₁ p μ) (hu₂ : MemLpLoc u₂ p μ) (he₁ : MemLpLoc e₁ p μ) (he₂ : MemLpLoc e₂ p μ)
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) {t : ι}
    (ht : MeasurableSet (s t) ∧ IsBounded (s t)) :
    eLpNorm u₁ p (μ.restrict (s t)) ≤
      (eLpNorm e₁ p (μ.restrict (s t)) + k₂ * eLpNorm e₂ p (μ.restrict (s t)) + β₂ + k₂ * β₁) /
      (1 - k₁ * k₂) := by
  have hk' : 0 < 1 - k₁ * k₂ := by simp [hk]
  norm_cast
  nth_rw 1 [ENNReal.le_div_iff_mul_le ?_ (by simp)]; swap
  · left
    rw [ENNReal.coe_ne_zero]
    apply hk'.ne'
  simp only [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_mul]
  rw [ENNReal.mul_sub (fun _ _ ↦ (hu₁ (s t) ht).eLpNorm_ne_top)]
  simp only [mul_one, tsub_le_iff_right]
  calc
    _ ≤ eLpNorm e₁ p (μ.restrict (s t)) + k₂ * eLpNorm u₂ p (μ.restrict (s t)) + β₂ := by
      exact smallGainThm_part1₁ hG₁ hG₂ hG₂' hp hu₂ he₁ h ht
    _ ≤ _ := by
      grw [smallGainThm_part1₂ hG₁ hG₁' hG₂ hp hu₁ he₂ h ht]
      ring_nf
      gcongr

theorem smallGainThm_part2₂
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    (hG₁' : G₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel)
    (hG₂' : G₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hp : 1 ≤ p) (hk : k₁ * k₂ < 1)
    {u₁ : α → E} {u₂ : α → F} {e₁ : α → E} {e₂ : α → F}
    (hu₁ : MemLpLoc u₁ p μ) (hu₂ : MemLpLoc u₂ p μ) (he₁ : MemLpLoc e₁ p μ) (he₂ : MemLpLoc e₂ p μ)
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (u₁ x, u₂ x)) ∈ loop.inputState) {t : ι}
    (ht : MeasurableSet (s t) ∧ IsBounded (s t)) :
    eLpNorm u₂ p (μ.restrict (s t)) ≤
      (eLpNorm e₂ p (μ.restrict (s t)) + k₁ * eLpNorm e₁ p (μ.restrict (s t)) + β₁ + k₁ * β₂) /
      (1 - k₁ * k₂) := by
  have hk' : 0 < 1 - k₁ * k₂ := by simp [hk]
  norm_cast
  nth_rw 1 [ENNReal.le_div_iff_mul_le ?_ (by simp)]; swap
  · left
    rw [ENNReal.coe_ne_zero]
    apply hk'.ne'
  simp only [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_mul]
  rw [ENNReal.mul_sub (fun _ _ ↦ (hu₂ (s t) ht).eLpNorm_ne_top)]
  simp only [mul_one, tsub_le_iff_right]
  calc
    _ ≤ eLpNorm e₂ p (μ.restrict (s t)) + k₁ * eLpNorm u₁ p (μ.restrict (s t)) + β₁ := by
      exact smallGainThm_part1₂ hG₁ hG₁' hG₂ hp hu₁ he₂ h ht
    _ ≤ _ := by
      grw [smallGainThm_part1₁ hG₁ hG₂ hG₂' hp hu₂ he₁ h ht]
      ring_nf
      gcongr

/-theorem smallGainThm_part3₁
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    (hG₁' : G₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel)
    (hG₂' : G₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hp : 1 ≤ p) (hk : k₁ * k₂ < 1)
    {y₁ : α → F} {y₂ : α → E} {e₁ : α → E} {e₂ : α → F}
    (hu₁ : MemLpLoc y₁ p μ) (hu₂ : MemLpLoc y₂ p μ) (he₁ : MemLpLoc e₁ p μ) (he₂ : MemLpLoc e₂ p μ)
    (h : (fun x ↦ (e₁ x, e₂ x), fun x ↦ (y₁ x, y₂ x)) ∈ loop.inputOutput) {t : ι}
    (ht : MeasurableSet (s t) ∧ IsBounded (s t)) :
    eLpNorm y₁ p (μ.restrict (s t)) ≤
      (eLpNorm e₁ p (μ.restrict (s t)) + k₂ * eLpNorm e₂ p (μ.restrict (s t)) + β₂ + k₂ * β₁) /
      (1 - k₁ * k₂) := by
  calc
    _ ≤ k₁ * eLpNorm sorry p (μ.restrict (s t)) + β₁ := by
      sorry
    _ ≤ k₁ * ((eLpNorm e₁ p _ + k₂ * eLpNorm e₂ p _ + β₂ + k₂ * β₁) / (1 - k₁ * k₂)) + β₁ := by
      sorry
    _ = (k₁ * eLpNorm e₁ p _ + k₁ * k₂ * eLpNorm e₂ p _ + k₁ * k₂ ) := by
      sorry-/

/-- The *small-gain theorem* states that if two maps `G₁` and `G₂` are finite gain stable with
gain less than `k₁` and `k₂`, respectively, and `k₁ * k₁ < 1`, then the closed feedback loop is
finite gain stable as well.

Version for the map from inputs to states. -/
theorem inputStateLp_isFiniteGainStableWith [hp : Fact (1 ≤ p)] (hp' : p ≠ ∞)
    {G₁ : (α → E) → α → F} (hG₁ : G₁.graph = loop.topRel)
    (hG₁' : G₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    {G₂ : (α → F) → α → E} (hG₂ : G₂.graph = loop.botRel)
    (hG₂' : G₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hk : k₁ * k₂ < 1)
    (ht : ∀ t, MeasurableSet (s t) ∧ IsBounded (s t)) :
    (loop.inputStateLp p).IsFiniteGainStableWith (loopGainLp p.toReal k₁ k₂) (loopBias k₁ k₂ β₁ β₂)
      s p μ := by
  intro t e u he hu heu
  rw [memLpLoc_withLp_prod_iff] at he hu
  let u₁ t := WithLp.fst (u t)
  have hu₁ : MemLpLoc u₁ p μ := hu.1
  let u₂ t := WithLp.snd (u t)
  have hu₂ : MemLpLoc u₂ p μ := hu.2
  let e₁ t := WithLp.fst (e t)
  have he₁ : MemLpLoc e₁ p μ := he.1
  let e₂ t := WithLp.snd (e t)
  have he₂ : MemLpLoc e₂ p μ := he.2
  calc
    _ ≤ eLpNorm u₁ p (μ.restrict (s t)) + eLpNorm u₂ p (μ.restrict (s t)) :=
      eLpNorm_withLp_prod_le_add hp' (hu₁ (s t) (ht t)).aestronglyMeasurable
    _ ≤ ((eLpNorm e₁ p (μ.restrict (s t)) + k₂ * eLpNorm e₂ p (μ.restrict (s t)) + β₂ + k₂ * β₁) /
        (1 - k₁ * k₂)) +
        ((eLpNorm e₂ p (μ.restrict (s t)) + k₁ * eLpNorm e₁ p (μ.restrict (s t)) + β₁ + k₁ * β₂) /
        (1 - k₁ * k₂)) := by
      gcongr
      · apply smallGainThm_part2₁ hG₁ hG₁' hG₂ hG₂' hp.out hk hu₁ hu₂ he₁ he₂ heu (ht t)
      · apply smallGainThm_part2₂ hG₁ hG₁' hG₂ hG₂' hp.out hk hu₁ hu₂ he₁ he₂ heu (ht t)
    _ = ((1 + k₁) * eLpNorm e₁ p (μ.restrict (s t)) + (1 + k₂) * eLpNorm e₂ p (μ.restrict (s t)) +
        (β₁ + β₂ + k₁ * β₂ + k₂ * β₁)) /
        (1 - k₁ * k₂) := by
      rw [ENNReal.div_add_div_same]
      congr 1; ring
    _ ≤ ((max (1 + k₁) (1 + k₂)) / (1 - k₁ * k₂)) *
        (eLpNorm e₁ p (μ.restrict (s t)) + eLpNorm e₂ p (μ.restrict (s t))) +
        (β₁ + β₂ + k₁ * β₂ + k₂ * β₁) / (1 - k₁ * k₂) := by
      rw [← ENNReal.mul_div_right_comm]
      rw [ENNReal.div_add_div_same]
      rw [mul_add]
      gcongr 4
      · simp
      · simp
    _ ≤ ((max (1 + k₁) (1 + k₂)) / (1 - k₁ * k₂)) *
        ((2 : ℝ≥0∞) ^ ((p.toReal - 1) / p.toReal) * eLpNorm e p (μ.restrict (s t))) +
        (β₁ + β₂ + k₁ * β₂ + k₂ * β₁) / (1 - k₁ * k₂) := by
      gcongr
      exact add_le_eLpNorm_withLp_prod hp' (he₁ (s t) (ht t)).aestronglyMeasurable
    _ = _ := by
      have hk' : 0 < 1 - k₁ * k₂ := by simp [hk]
      rw [← mul_assoc]
      congr 2
      · unfold loopGainLp
        rw [ENNReal.coe_div hk'.ne']
        rw [← ENNReal.mul_div_right_comm]
        congr
        rw [ENNReal.coe_max, ENNReal.coe_mul]
        have : 0 ≤ (p.toReal - 1) := by
          rw [sub_nonneg, ← ENNReal.ofReal_le_iff_le_toReal hp']
          simp [hp.out]
        rw [ENNReal.coe_rpow_of_nonneg 2 (by positivity)]
        simp
        ring
      · unfold loopBias
        simp [ENNReal.coe_div hk'.ne']

end SetRel.closedLoop

variable (f : α → E × F)

variable (α E F) in
/-- A closed loop -/
structure Function.closedLoop where
  /-- foo -/
  topFun : (α → E) → α → F
  /-- bar -/
  botFun : (α → F) → α → E

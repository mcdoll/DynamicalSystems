/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability
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
theorem isCausal (h_topRel : loop.topRel.IsCausal s p μ) (h_botRel : loop.botRel.IsCausal s p μ) :
    loop.inputOutput.IsCausal s p μ := by
  constructor
  · intro e y hey he
    simp only [mem_inputOutput] at hey
    -- seems like we have to assume something here
    have := h_topRel.memLpLoc hey.1
    sorry
  · intro t e y e' y' hey hey' he hy he' hy' hee'
    have htop := h_topRel.causal t
    have hbot := h_botRel.causal t
    sorry

end SetRel.closedLoop

variable (f : α → E × F)

variable (α E F) in
/-- A closed loop -/
structure Function.closedLoop where
  /-- foo -/
  topFun : (α → E) → α → F
  /-- bar -/
  botFun : (α → F) → α → E

/-- The relation from inputs to outputs -/
def inputOutputRel (loop : Function.closedLoop α E F) : SetRel (α → E × F) (α → E × F) := sorry

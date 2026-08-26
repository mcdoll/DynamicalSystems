/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Stability
public import DynamicalSystems.Basic.WithLp

/-! # Stability of product maps

We prove that `f` and `g` are finite gain stable, then `x ↦ (f x, g x)` is finite gain stable.

-/

/-

Application: `G₁ : (α → E) → α → F`, `G₂ : (α → F) → α → E`

and `R₁ : SetRel (α → WithLp p (E × F)) (α → WithLp p (E × F))` then
`R₂ = (G₁, G₂).graph.comp R₁` is stable

need to make sense of `(G₁, G₂)`.as a map `(α → WithLp p (E × F)) → α → WithLp p (E × F)`



-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

variable {ι α E₁ E₂ F₁ F₂ : Type*}


variable {f₁ : (α → E₁) → α → F₁} {f₂ : (α → E₂) → α → F₂}

variable {s : ι → Set α} {p : ℝ≥0∞}

/-- The pair `(f₁, f₂)` as map `(α → WithLp p (E₁ × E₂)) → α → WithLp p (F₁ × F₂)`. -/
def mapProdLp (p : ℝ≥0∞) (f₁ : (α → E₁) → α → F₁) (f₂ : (α → E₂) → α → F₂)
    (u : α → WithLp p (E₁ × E₂)) (x : α) : WithLp p (F₁ × F₂) :=
  WithLp.toLp p (f₁ (WithLp.fst ∘ u) x, f₂ (WithLp.snd ∘ u) x)

theorem mapProdLp_apply (u : α → WithLp p (E₁ × E₂)) (x : α) :
    mapProdLp p f₁ f₂ u x = WithLp.toLp p (f₁ (WithLp.fst ∘ u) x, f₂ (WithLp.snd ∘ u) x) := by
  rfl

@[simp]
theorem fst_mapProdLp_apply (u : α → WithLp p (E₁ × E₂)) (x : α) :
    (mapProdLp p f₁ f₂ u x).fst = f₁ (WithLp.fst ∘ u) x := by
  rfl

@[simp]
theorem snd_mapProdLp_apply (u : α → WithLp p (E₁ × E₂)) (x : α) :
    (mapProdLp p f₁ f₂ u x).snd = f₂ (WithLp.snd ∘ u) x := by
  rfl

variable [MeasurableSpace α] [TopologicalSpace α]
  [NormedAddCommGroup E₁] [NormedAddCommGroup F₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup F₂]

variable {μ : Measure α} {k₁ k₂ β₁ β₂ : ℝ≥0}

theorem isFiniteGainStableWith_mapProdLp [Fact (1 ≤ p)]
    (hf₁ : f₁.IsFiniteGainStableWith k₁ β₁ s p μ)
    (hf₂ : f₂.IsFiniteGainStableWith k₂ β₂ s p μ) (hs : ∀ t, IsCompact (s t)) :
    (mapProdLp p f₁ f₂).IsFiniteGainStableWith
      (max k₁ k₂ * (addLEConst p).toNNReal) (β₁ + β₂) s p μ := by
  constructor
  · intro u hu
    rw [memLpLoc_withLp_prod_iff] at hu ⊢
    exact ⟨hf₁.memLpLoc hu.1, hf₂.memLpLoc hu.2⟩
  · intro t u hu
    calc
      _ ≤ eLpNorm (f₁ (WithLp.fst ∘ u)) p _ + eLpNorm (f₂ (WithLp.snd ∘ u)) p _ := by
        apply eLpNorm_withLp_prod_le_add
        rw [memLpLoc_withLp_prod_iff] at hu
        exact (hf₁.memLpLoc hu.1).aestronglyMeasurable (hs t)
      _ ≤ (k₁ * eLpNorm (WithLp.fst ∘ u) p _ + β₁) + (k₂ * eLpNorm (WithLp.snd ∘ u) p _ + β₂) := by
        rw [memLpLoc_withLp_prod_iff] at hu
        gcongr
        · exact hf₁.stableWith _ _ hu.1
        · exact hf₂.stableWith _ _ hu.2
      _ ≤ ((max k₁ k₂) * eLpNorm (WithLp.fst ∘ u) p _ + β₁) +
          ((max k₁ k₂) * eLpNorm (WithLp.snd ∘ u) p _ + β₂) := by
        gcongr
        · simp
        · simp
      _ = (max k₁ k₂) * (eLpNorm (WithLp.fst ∘ u) p _ +
          eLpNorm (WithLp.snd ∘ u) p _) + (β₁ + β₂) := by
        ring
      _ ≤ _ := by
        norm_cast
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by simp), mul_assoc]
        have : u = (fun x ↦ WithLp.toLp p ((WithLp.fst ∘ u) x, (WithLp.snd ∘ u) x)) := by
          ext x
          rw [WithLp.ext_iff]
          ext; all_goals simp
        nth_rw 3 [this]
        gcongr
        apply add_le_eLpNorm_withLp_prod
        rw [memLpLoc_withLp_prod_iff] at hu
        exact hu.1.aestronglyMeasurable (hs t)

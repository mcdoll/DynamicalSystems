/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Missing calculus lemmas -/

@[expose] public noncomputable section

variable {E E' F G : Type*}

section uncurry

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- todo: generalize to `𝕜`
  {x : E} {y : E'}


theorem foo₀ {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E') :
    fderiv ℝ f (x, y) (0, v) = fderiv ℝ (fun z ↦ f (x, z)) y v := by
  calc
    _ = (fderiv ℝ f (x, y) ∘SL (fderiv ℝ (fun z ↦ (x, z)) y)) v := by
      simp [(differentiableAt_const x).fderiv_prodMk (differentiableAt_fun_id)]
    _ = _ := by
      congr
      apply (fderiv_comp (x := y) hf (by fun_prop)).symm

theorem foo₀' {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E) :
    fderiv ℝ f (x, y) (v, 0) = fderiv ℝ (fun z ↦ f (z, y)) x v := by
  calc
    _ = (fderiv ℝ f (x, y) ∘SL (fderiv ℝ (fun z ↦ (z, y)) x)) v := by
      simp [(differentiableAt_fun_id).fderiv_prodMk]
    _ = _ := by
      congr
      apply (fderiv_comp (x := x) hf (by fun_prop)).symm

theorem fderiv_prod (f : E × E' → F) (hf : DifferentiableAt ℝ f (x, y)) :
    fderiv ℝ f (x, y) =
      (fderiv ℝ (fun x ↦ f (x, y)) x).coprod (fderiv ℝ (fun y ↦ f (x, y)) y) := by
  ext z
  · simp [foo₀' hf]
  · simp [foo₀ hf]

theorem fderiv_uncurry (f : E → E' → F) (hf : DifferentiableAt ℝ f.uncurry (x, y)) :
    fderiv ℝ f.uncurry (x, y) = (fderiv ℝ (f · y) x).coprod (fderiv ℝ (f x) y) := by
  apply fderiv_prod f.uncurry hf


end uncurry

section deriv_prod

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_prodMk {f : ℝ → E} {g : ℝ → F} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) :
    deriv (fun s ↦ (f s, g s)) t = (deriv f t, deriv g t) :=
  (hf.prodMk hg).hasDerivAt.unique (hf.hasDerivAt.prodMk hg.hasDerivAt)

@[simp]
theorem fst_deriv_prodMk {f : ℝ → E} {g : ℝ → F} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) :
    (deriv (fun s ↦ (f s, g s)) t).fst = deriv f t := by
  rw [deriv_prodMk hf hg]

@[simp]
theorem snd_deriv_prodMk {f : ℝ → E} {g : ℝ → F} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) :
    (deriv (fun s ↦ (f s, g s)) t).snd = deriv g t := by
  rw [deriv_prodMk hf hg]

end deriv_prod

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {Φ : ℝ → E → E} {f : ℝ → E → E} {v : ℝ → E → E} {x₀ : E} (s : Set ℝ) {t : ℝ}

theorem foo₁' {f : ℝ → E → F} {g : ℝ → E} (hf : DifferentiableAt ℝ f.uncurry (t, g t))
    (hg : DifferentiableAt ℝ g t) :
    deriv (fun s ↦ f s (g s)) t = deriv (f · (g t)) t + fderiv ℝ (f t) (g t) (deriv g t) := calc
  _ = deriv (fun s ↦ f.uncurry (s, (g s))) t := by simp
  _ = (fderiv ℝ f.uncurry (t, g t)) (deriv (fun s ↦ (s, g s)) t) := by
    have hg' : DifferentiableAt ℝ (fun s ↦ (s, g s)) t := by fun_prop
    exact fderiv_comp_deriv t hf hg'
  _ = _ := by
    simp [fderiv_uncurry f hf, hg]

theorem foo₂' {f : ℝ → E → F → G} {g₁ : ℝ → E} {g₂ : ℝ → F}
    (hf : DifferentiableAt ℝ (fun t ↦ (f t ·).uncurry).uncurry (t, g₁ t, g₂ t))
    (hg₁ : DifferentiableAt ℝ g₁ t) (hg₂ : DifferentiableAt ℝ g₂ t) :
    deriv (fun s ↦ f s (g₁ s) (g₂ s)) t =
      deriv (f · (g₁ t) (g₂ t)) t +
      fderiv ℝ (f t · (g₂ t)) (g₁ t) (deriv g₁ t) +
      fderiv ℝ (f t (g₁ t)) (g₂ t) (deriv g₂ t) := by
  let f' := fun t ↦ f t (g₁ t)
  calc
    _ = deriv (fun s ↦ f'.uncurry (s, (g₂ s))) t := by simp [f']
    _ = deriv (f' · (g₂ t)) t + fderiv ℝ (f' t) (g₂ t) (deriv g₂ t) := by
      exact foo₁' (by fun_prop) hg₂
    _ = _ := by
      congr
      exact foo₁' (f := (f · · (g₂ t))) (by fun_prop) hg₁


theorem foo₁ (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) (hΦ : DifferentiableAt ℝ (Φ · x₀) t) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (deriv (Φ · x₀) t) := by
  apply foo₁' hv hΦ

/-theorem foo₂ (hΦ : IsFundamentalSolution Φ f) (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (f t (Φ t x₀)) := by
  rw [foo₁ hv (hΦ.isIntegralCurve x₀ t).differentiableAt, hΦ.deriv x₀]-/

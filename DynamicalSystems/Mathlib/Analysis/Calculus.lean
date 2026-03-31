/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public noncomputable section

variable {E E' F : Type*}

section uncurry

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- todo: generalize to `𝕜`
  {x : E} {y : E'}


theorem bar {f : E → E' → F} {f₁ : E →L[ℝ] F} {f₂ : E' →L[ℝ] F}
    (hf₁ : HasFDerivAt (f · y) f₁ x) (hf₂ : HasFDerivAt (f x) f₂ y) :
    HasFDerivAt f.uncurry (f₁.coprod f₂) (x, y) := by
  sorry

theorem foo₀ {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E') :
    fderiv ℝ f (x, y) (0, v) = fderiv ℝ (fun z ↦ f (x, z)) y v := by
  calc
    _ = fderiv ℝ f (x, y) ((fderiv ℝ (fun z ↦ (x, z)) y) v) := by
      simp [(differentiableAt_const x).fderiv_prodMk (differentiableAt_fun_id)]
    _ = _ := by
      have hg : DifferentiableAt ℝ (fun z ↦ (x, z)) y := by fun_prop
      have := fderiv_comp (x := y) hf hg
      rw [ContinuousLinearMap.ext_iff] at this
      apply (this v).symm

theorem foo₀' {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E) :
    fderiv ℝ f (x, y) (v, 0) = fderiv ℝ (fun z ↦ f (z, y)) x v := by
  calc
    _ = fderiv ℝ f (x, y) ((fderiv ℝ (fun z ↦ (z, y)) x) v) := by
      simp [(differentiableAt_fun_id).fderiv_prodMk]
    _ = _ := by
      have hg : DifferentiableAt ℝ (fun z ↦ (z, y)) x := by fun_prop
      have := fderiv_comp (x := x) hf hg
      rw [ContinuousLinearMap.ext_iff] at this
      apply (this v).symm

theorem fderiv_uncurry (f : E → E' → F) (hf : DifferentiableAt ℝ f.uncurry (x, y)) :
    fderiv ℝ f.uncurry (x, y) = (fderiv ℝ (f · y) x).coprod (fderiv ℝ (f x) y) := by
  ext z
  · simp [foo₀' hf]
  · simp [foo₀ hf]

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

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Φ : ℝ → E → E} {f : ℝ → E → E} {v : ℝ → E → E} {x₀ : E} (s : Set ℝ) {t : ℝ}

theorem foo₁ (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) (hΦ : DifferentiableAt ℝ (Φ · x₀) t) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (deriv (Φ · x₀) t) := by
  calc
    _ = deriv (fun s ↦ v.uncurry (s, (Φ s x₀))) t := by simp
    _ = (fderiv ℝ (Function.uncurry v) (t, Φ t x₀)) (deriv (fun s ↦ (s, Φ s x₀)) t) := by
      have hΦ' : DifferentiableAt ℝ (fun s ↦ (s, Φ s x₀)) t := by fun_prop
      apply fderiv_comp_deriv t hv hΦ'
    _ = deriv (fun x ↦ v x (Φ t x₀)) t + (fderiv ℝ (v t) (Φ t x₀)) (deriv (fun x ↦ Φ x x₀) t) := by
      rw [fderiv_uncurry v hv]
      simp only [ContinuousLinearMap.coprod_apply, fderiv_eq_smul_deriv]
      congr
      · simp [hΦ]
      · simp [hΦ]

/-theorem foo₂ (hΦ : IsFundamentalSolution Φ f) (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (f t (Φ t x₀)) := by
  rw [foo₁ hv (hΦ.isIntegralCurve x₀ t).differentiableAt, hΦ.deriv x₀]-/

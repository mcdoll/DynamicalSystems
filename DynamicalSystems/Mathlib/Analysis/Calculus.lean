/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public noncomputable section

variable {E E' F : Type*}

section uncurry

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- todo: generalize to `𝕜`
  {x : E} {y : E'}

theorem foo₀ {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E') :
    fderiv ℝ f (x, y) (0, v) = fderiv ℝ (fun z ↦ f (x, z)) y v := by
  have hg : DifferentiableAt ℝ (fun z ↦ (x, z)) y := by fun_prop
  have := fderiv_comp (x := y) hf hg
  have this' : ((fderiv ℝ (fun z ↦ (x, z)) y) v) = (0, v) := by
    simp [(differentiableAt_const x).fderiv_prodMk (differentiableAt_fun_id)]
  rw [ContinuousLinearMap.ext_iff] at this
  specialize this v
  simp at this
  rw [this'] at this
  exact this.symm

theorem foo₀' {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E) :
    fderiv ℝ f (x, y) (v, 0) = fderiv ℝ (fun z ↦ f (z, y)) x v := by
  -- this follows from either `flip` or the same argument as above
  sorry

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
    (deriv (fun s ↦ (f s, g s)) t) = (deriv f t, deriv g t) :=
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

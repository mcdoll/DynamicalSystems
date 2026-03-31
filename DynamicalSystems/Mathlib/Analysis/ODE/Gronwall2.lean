module

public import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Order.Interval.Set.UnorderedInterval

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Set NNReal

variable {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g f' g' : ℝ → E} {a b t₀ : ℝ} {εf εg δ : ℝ}

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem₀
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) := by
  sorry

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem'
    (hv : ∀ t ∈ Icc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Icc a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ Icc a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Icc a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ Icc a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) :=
  dist_le_of_approx_trajectories_ODE_of_mem (hv · <| Set.Ico_subset_Icc_self ·)
    hf (hf' · <| Set.Ico_subset_Icc_self ·) (f_bound · <| Set.Ico_subset_Icc_self ·)
    (hfs · <| Set.Ico_subset_Icc_self ·) hg (hg' · <| Set.Ico_subset_Icc_self ·)
    (g_bound · <| Set.Ico_subset_Icc_self ·) (hgs · <| Set.Ico_subset_Icc_self ·) ha

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem''
    (hv : ∀ t ∈ uIcc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (uIcc a b))
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (f_bound : ∀ t ∈ uIcc a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ uIcc a b, f t ∈ s t)
    (hg : ContinuousOn g (uIcc a b))
    (hg' : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t)
    (g_bound : ∀ t ∈ uIcc a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ uIcc a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) (t : ℝ) (ht : t ∈ uIcc a b) :
    dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) |t - a| := by
  by_cases! h : a ≤ b
  · have : 0 ≤ t - a := by
      simp only [h, uIcc_of_le, mem_Icc] at ht
      simpa using ht.1
    simp only [h, uIcc_of_le] at *
    rw [abs_eq_self.mpr this]
    apply dist_le_of_approx_trajectories_ODE_of_mem' hv hf (hf' · · |>.hasDerivWithinAt) f_bound hfs
      hg (hg' · · |>.hasDerivWithinAt) g_bound hgs ha t ht
  · have : t - a ≤ 0 := by
      simp [h.le] at ht
      simpa using ht.2
    let f₀ := (f <| -·)
    let g₀ := (g <| -·)
    simp only [h.le, uIcc_of_ge, mem_Icc] at ht
    simp only [h.le, uIcc_of_ge, mem_Icc] at *
    calc
      _ = dist (f (- (-t))) (g (- (-t))) := by rw [neg_neg]
      _ ≤ gronwallBound δ (↑K) (εf + εg) ((-t) - (-a)) := by
        have hv₀ : ∀ t ∈ Icc (-a) (-b), LipschitzOnWith K (-v (-t)) (s (-t)) := by
          intro t ht
          apply LipschitzOnWith.neg
          exact hv (-t) (by grind)
        have hf₀ : ContinuousOn (f <| -·) (Icc (-a) (-b)) := by
          intro t ht
          apply (hf (-t) (by grind)).comp (by fun_prop)
          intro; grind
        have hf'₀ : ∀ t ∈ Icc (-a) (-b), HasDerivAt (f <| -·) (-f' (-t)) t := by
          intro t ht
          have := hf' (-t) (by grind)
          have this' := hasDerivAt_neg t
          convert this.scomp t this' using 1
          simp
        have f_bound₀ : ∀ t ∈ Icc (-a) (-b), dist ((-f' <| -·) t) (-v (-t) (f (-t))) ≤ εf := by
          intro t ⟨ht₀, ht₁⟩
          simp only [Pi.neg_apply, dist_neg_neg, ge_iff_le]
          exact f_bound (-t) (by grind)
        have hfs₀ : ∀ t ∈ Icc (-a) (-b), (f <| -·) t ∈ s (-t) := by
          intro t ht
          exact hfs (-t) (by grind)
        have hg₀ : ContinuousOn (g <| -·) (Icc (-a) (-b)) := by
          intro t ht
          apply (hg (-t) (by grind)).comp (by fun_prop)
          intro; grind
        have hg'₀ : ∀ t ∈ Icc (-a) (-b), HasDerivAt (g <| -·) (-g' (-t)) t := by
          intro t ht
          have := hg' (-t) (by grind)
          have this' := hasDerivAt_neg t
          convert this.scomp t this' using 1
          simp
        have g_bound₀ : ∀ t ∈ Icc (-a) (-b), dist ((-g' <| -·) t) (-v (-t) (g (-t))) ≤ εg := by
          intro t ⟨ht₀, ht₁⟩
          simp only [Pi.neg_apply, dist_neg_neg, ge_iff_le]
          exact g_bound (-t) (by grind)
        have hgs₀ : ∀ t ∈ Icc (-a) (-b), (g <| -·) t ∈ s (-t) := by
          intro t ht
          exact hgs (-t) (by grind)
        apply dist_le_of_approx_trajectories_ODE_of_mem' hv₀ hf₀
          (hf'₀ · · |>.hasDerivWithinAt) f_bound₀ hfs₀ hg₀  (hg'₀ · · |>.hasDerivWithinAt) g_bound₀
          hgs₀ (by simp [ha]) (-t) (by simp [ht])
      _ = gronwallBound δ K (εf + εg) (|t - a|) := by
        congr
        grind

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem'
    (hv : ∀ t ∈ uIcc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (uIcc a b))
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ uIcc a b, f t ∈ s t)
    (hg : ContinuousOn g (uIcc a b))
    (hg' : ∀ t ∈ uIcc a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ uIcc a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ uIcc a b, dist (f t) (g t) ≤ δ * Real.exp (K * |t - a|) := by
  have f_bound : ∀ t ∈ uIcc a b, dist (v t (f t)) (v t (f t)) ≤ 0 := by intros; rw [dist_self]
  have g_bound : ∀ t ∈ uIcc a b, dist (v t (g t)) (v t (g t)) ≤ 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem'' hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this

theorem dist_le_of_trajectories_ODE'
    (hv : ∀ t ∈ uIcc a b, LipschitzWith K (v t))
    (hf : ContinuousOn f (uIcc a b))
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f (v t (f t)) t)
    (hg : ContinuousOn g (uIcc a b))
    (hg' : ∀ t ∈ uIcc a b, HasDerivAt g (v t (g t)) t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ uIcc a b, dist (f t) (g t) ≤ δ * Real.exp (K * |t - a|) :=
  dist_le_of_trajectories_ODE_of_mem' (hv · · |>.lipschitzOnWith) hf hf'
    (fun _ _ ↦ Set.mem_univ _) hg hg' (fun _ _ ↦ Set.mem_univ _) ha

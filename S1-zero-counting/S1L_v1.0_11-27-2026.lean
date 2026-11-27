/-
Schoenfeld S1, part L: a continuous argument of `xi` along the path `2 → 2 + iT → 1/2 + iT` with
`Θ 0 = 0` and `Θ 2 = π + rsTheta T + π S(T)` (`exists_arg_xi_path`).
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldS1.X
import SchoenfeldS1.D3
import SchoenfeldS1.B

namespace SchoenfeldS1

open Complex Real Set
open TauCeti.LFunctions (riemannZetaS riemannZetaSPath riemannZetaSPath_of_le_one
  riemannZetaSPath_of_one_le exists_riemannZetaS_eq_div_pi riemannZetaSPath_ne_one
  isPiecewiseC1On_riemannZetaSPath)

local notation "ζ" => riemannZeta

/-! ### Polar forms -/

lemma polar_mul {a b : ℂ} {x y : ℝ} (ha : a = ‖a‖ * exp (I * x)) (hb : b = ‖b‖ * exp (I * y)) :
    a * b = ‖a * b‖ * exp (I * ((x + y : ℝ) : ℂ)) := by
  rw [norm_mul]
  conv_lhs => rw [ha, hb]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

lemma polar_of_arg (x : ℂ) : x = ‖x‖ * exp (I * ((arg x : ℝ) : ℂ)) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I x]
  rw [mul_comm I]

lemma polar_exp (w : ℂ) : exp w = ‖exp w‖ * exp (I * ((w.im : ℝ) : ℂ)) := by
  rw [Complex.norm_exp, ofReal_exp]
  conv_lhs => rw [← re_add_im w, Complex.exp_add]
  congr 1
  ring_nf

/-! ### The path -/

variable {T : ℝ}

lemma re_path_ge (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) : 1 / 2 ≤ (riemannZetaSPath T u).re := by
  rcases le_total u 1 with h | h
  · rw [riemannZetaSPath_of_le_one h]; simp; norm_num
  · rw [riemannZetaSPath_of_one_le h]; simp; linarith [hu.2]

lemma im_path_nonneg (hT : 0 < T) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) :
    0 ≤ (riemannZetaSPath T u).im := by
  rcases le_total u 1 with h | h
  · rw [riemannZetaSPath_of_le_one h]; simp; exact mul_nonneg hu.1 hT.le
  · rw [riemannZetaSPath_of_one_le h]; simp; exact hT.le

lemma path_mem_slitPlane (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) : riemannZetaSPath T u ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by linarith [re_path_ge (T := T) u hu]))

lemma path_sub_one_mem_slitPlane (hT : 0 < T) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) :
    riemannZetaSPath T u - 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases le_total u 1 with h | h
  · rw [riemannZetaSPath_of_le_one h]
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · left; rw [← h0]; simp
    · right; simp; exact ⟨h0.ne', hT.ne'⟩
  · rw [riemannZetaSPath_of_one_le h]; right; simp; exact hT.ne'

lemma continuousOn_path : ContinuousOn (riemannZetaSPath T) (Icc 0 2) := by
  have := (isPiecewiseC1On_riemannZetaSPath T).continuousOn
  rwa [uIcc_of_le zero_le_two] at this

/-- The `s (s - 1)` factor along the path: continuous argument `arg s + arg (s - 1)`. -/
lemma polar_quad (u : ℝ) : riemannZetaSPath T u * (riemannZetaSPath T u - 1) =
    ‖riemannZetaSPath T u * (riemannZetaSPath T u - 1)‖ *
      exp (I * ((arg (riemannZetaSPath T u) + arg (riemannZetaSPath T u - 1) : ℝ) : ℂ)) :=
  polar_mul (polar_of_arg _) (polar_of_arg _)

lemma continuousOn_argQuad (hT : 0 < T) :
    ContinuousOn (fun u => arg (riemannZetaSPath T u) + arg (riemannZetaSPath T u - 1)) (Icc 0 2) := by
  apply ContinuousOn.add
  · intro u hu
    exact (continuousAt_arg (path_mem_slitPlane u hu)).comp_continuousWithinAt (continuousOn_path u hu)
  · intro u hu
    have hf : ContinuousWithinAt (fun u => riemannZetaSPath T u - 1) (Icc 0 2) u :=
      (continuousOn_path u hu).sub continuousWithinAt_const
    exact (continuousAt_arg (path_sub_one_mem_slitPlane hT u hu)).comp_continuousWithinAt
      (f := fun u => riemannZetaSPath T u - 1) hf

lemma argQuad_zero : arg (2 : ℂ) + arg (1 : ℂ) = 0 := by
  have h2 : arg (2 : ℂ) = 0 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
  rw [h2, arg_one, add_zero]

lemma argQuad_two (hT : 0 < T) : arg (1 / 2 + T * I : ℂ) + arg (1 / 2 + T * I - 1 : ℂ) = π := by
  have e : (1 / 2 + T * I - 1 : ℂ) = -1 / 2 + T * I := by ring
  rw [e, arg_of_re_nonneg (by norm_num),
    arg_of_re_neg_of_im_nonneg (by norm_num) (by simp; exact hT.le)]
  have hn : ‖(1 / 2 + T * I : ℂ)‖ = ‖(-1 / 2 + T * I : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [normSq_apply]
    ring
  have hi1 : (1 / 2 + T * I : ℂ).im = T := by simp
  have hi2 : (-(-1 / 2 + T * I : ℂ)).im = -T := by simp
  rw [hi1, hi2, hn]
  simp only [neg_div, Real.arcsin_neg]
  ring

/-- The `Γℝ` factor along the path: `Γℝ s = exp w` with
`w = log π · (-s/2) + logGamma (s/2)`. -/
noncomputable def wG (s : ℂ) : ℂ := (Real.log π : ℂ) * (-s / 2) + TauCeti.logGamma (s / 2)

lemma Gammaℝ_eq_exp_wG {s : ℂ} (hs : 0 < s.re) : Gammaℝ s = exp (wG s) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : s / 2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  rw [Gammaℝ_def, cpow_def_of_ne_zero hpi, ← TauCeti.exp_logGamma h2, ← Complex.exp_add, wG,
    ofReal_log Real.pi_pos.le]

lemma polar_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    Gammaℝ s = ‖Gammaℝ s‖ * exp (I * (((wG s).im : ℝ) : ℂ)) := by
  rw [Gammaℝ_eq_exp_wG hs]
  exact polar_exp _

lemma continuousOn_wG : ContinuousOn wG {s : ℂ | 0 < s.re} := by
  have h1 : Continuous (fun s : ℂ => (Real.log π : ℂ) * (-s / 2)) := by fun_prop
  have h2 : ContinuousOn (fun s : ℂ => TauCeti.logGamma (s / 2)) {s : ℂ | 0 < s.re} := by
    refine TauCeti.differentiableOn_logGamma.continuousOn.comp
      (continuous_id.div_const (2 : ℂ)).continuousOn ?_
    intro s hs
    have hs' : 0 < s.re := hs
    exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  unfold wG
  exact h1.continuousOn.add h2

lemma wG_two_im : (wG 2).im = 0 := by
  unfold wG
  rw [show (2 : ℂ) / 2 = 1 by norm_num, TauCeti.logGamma_one]
  simp

lemma wG_half_add_im (T : ℝ) : (wG (1 / 2 + T * I)).im = rsTheta T := by
  unfold wG rsTheta
  have e : (1 / 2 + T * I : ℂ) / 2 = zTheta T := by
    apply Complex.ext <;> simp [zTheta]; ring
  rw [e]
  simp
  ring

/-- **A continuous argument of `xi` along the path `2 → 2 + iT → 1/2 + iT`**, starting at `0` and
ending at `π + rsTheta T + π S(T)`. -/
theorem exists_arg_xi_path (hT : 14 ≤ T) (hord : NotOrdinate T) :
    ∃ Θ : ℝ → ℝ, ContinuousOn Θ (Icc 0 2) ∧
      (∀ u ∈ Icc (0 : ℝ) 2, xi (riemannZetaSPath T u) =
        ‖xi (riemannZetaSPath T u)‖ * exp (I * Θ u)) ∧
      Θ 0 = 0 ∧ Θ 2 = π + rsTheta T + π * riemannZetaS T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨φ, hφ, hlift, hφ0, hS⟩ := exists_riemannZetaS_eq_div_pi hT0.ne' hord
  refine ⟨fun u => (arg (riemannZetaSPath T u) + arg (riemannZetaSPath T u - 1)) +
      (wG (riemannZetaSPath T u)).im + φ u, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.add (ContinuousOn.add (continuousOn_argQuad hT0) ?_) hφ
    exact Complex.continuous_im.comp_continuousOn (continuousOn_wG.comp continuousOn_path
      fun u hu => by
        show 0 < (riemannZetaSPath T u).re
        linarith [re_path_ge (T := T) u hu])
  · intro u hu
    have hre := re_path_ge (T := T) u hu
    have hs0 : riemannZetaSPath T u ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have hs1 : riemannZetaSPath T u ≠ 1 := riemannZetaSPath_ne_one hT0.ne' u
    rw [xi_eq_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos (by linarith))]
    have h1 := polar_quad (T := T) u
    have h2 := polar_Gammaℝ (s := riemannZetaSPath T u) (by linarith)
    have h3 := hlift u hu
    have := polar_mul h1 (polar_mul h2 h3)
    conv_lhs => rw [this]
    congr 2
    push_cast
    ring
  · simp only [TauCeti.LFunctions.riemannZetaSPath_zero, wG_two_im, hφ0]
    rw [show (2 : ℂ) - 1 = 1 by norm_num, argQuad_zero]
    ring
  · simp only [TauCeti.LFunctions.riemannZetaSPath_two, wG_half_add_im]
    rw [argQuad_two hT0, hS, mul_div_cancel₀ _ Real.pi_pos.ne']

end SchoenfeldS1

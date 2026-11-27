/-
Schoenfeld S1, part M: the Riemann-von Mangoldt identity `N(T) = θ(T)/π + 1 + S(T)` for `T ≥ 14`
not an ordinate (`NT_eq_rsTheta_add`), from the argument principle on the rectangle
`[-1, 2] × [0, T]` (`SchoenfeldS1.R`) and the explicit continuous argument of `xi` along the
L-path (`SchoenfeldS1.L`), cell by cell along `rectBoundary (-1) (2 + iT)`.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldS1.L
import SchoenfeldS1.R

/-!
# The five boundary cells

`rectBoundary (-1) (2 + iT)` on `[0, 4]`: bottom `[0, 1]` (real axis, argument `0`), right `[1, 2]`
(`= p (t - 1)`, argument `Θ (t - 1)`), top-right `[2, 5/2]` (`= p (2t - 3)`, argument `Θ (2t - 3)`),
top-left `[5/2, 3]` (`= 1 - conj (p (7 - 2t))`, argument `-Θ (7 - 2t)` by `xi_one_sub`, `xi_conj`),
left `[3, 4]` (`= 1 - conj (p (4 - t))`, argument `-Θ (4 - t)`), where `p = riemannZetaSPath T` and
`Θ` is the argument of `SchoenfeldS1.L`. Each cell variation of the global argument `θ` equals that
of the explicit one (`TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp`); telescoping,
`θ 4 - θ 0 = 2 Θ 2 = 2 (π + rsTheta T + π S(T))`, and `rect_arg_sub_eq_two_pi_mul_NT` gives
`2 π N(T)` for the same quantity.
-/

namespace SchoenfeldS1

open Complex Real Set ComplexConjugate TauCeti TauCeti.Contour
open TauCeti.LFunctions (riemannZetaS riemannZetaSPath riemannZetaSPath_of_le_one
  riemannZetaSPath_of_one_le)

variable {T : ℝ}

/-- Conjugation negates a continuous argument. -/
lemma polar_conj {z : ℂ} {x : ℝ} (hz : z = ‖z‖ * exp (I * x)) :
    conj z = ‖conj z‖ * exp (I * ((-x : ℝ) : ℂ)) := by
  rw [Complex.norm_conj]
  conv_lhs => rw [hz]
  rw [map_mul, conj_ofReal, ← Complex.exp_conj, map_mul, conj_I, conj_ofReal]
  push_cast
  ring_nf

/-- A positive real has the argument `0`. -/
lemma polar_ofReal_pos (σ : ℝ) : xi σ = ‖xi σ‖ * exp (I * ((0 : ℝ) : ℂ)) := by
  obtain ⟨h, hpos⟩ := xi_ofReal_pos σ
  rw [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, h, norm_real, Real.norm_of_nonneg hpos.le]

/-- The variation of the global argument `θ` on a cell `[a, b]` equals the variation of any
explicit continuous argument `ψ` on that cell. -/
lemma cell_var (hord : NotOrdinate T) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc 0 4)
    {θ ψ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 4))
    (hθl : ∀ t ∈ Icc (0 : ℝ) 4, xi (rectBoundary (-1 : ℂ) (2 + T * I) t) =
      ‖xi (rectBoundary (-1 : ℂ) (2 + T * I) t)‖ * exp (I * θ t))
    (hψ : ContinuousOn ψ (Icc a b))
    (hψl : ∀ t ∈ Icc a b, xi (rectBoundary (-1 : ℂ) (2 + T * I) t) =
      ‖xi (rectBoundary (-1 : ℂ) (2 + T * I) t)‖ * exp (I * ψ t)) :
    θ b - θ a = ψ b - ψ a :=
  sub_eq_sub_of_eq_norm_mul_exp (f := fun t => xi (rectBoundary (-1 : ℂ) (2 + T * I) t))
    isPreconnected_Icc (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (fun t _ => xi_ne_zero_frontier hord _ (rectBoundary_mem_frontier t))
    (hθ.mono hsub) hψ (fun t ht => hθl t (hsub ht)) hψl

/-! ### The cell parametrizations -/

lemma rb_zero_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rectBoundary (-1 : ℂ) (2 + T * I) t = ((-1 + 3 * t : ℝ) : ℂ) := by
  rw [rectBoundary_of_mem_Icc_zero_one ht]
  apply Complex.ext <;> simp <;> ring

lemma rb_one_two {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    rectBoundary (-1 : ℂ) (2 + T * I) t = riemannZetaSPath T (t - 1) := by
  rw [rectBoundary_of_mem_Icc_one_two ht, riemannZetaSPath_of_le_one (by linarith [ht.2])]
  apply Complex.ext <;> simp <;> ring

lemma rb_two_half {t : ℝ} (ht : t ∈ Icc (2 : ℝ) (5 / 2)) :
    rectBoundary (-1 : ℂ) (2 + T * I) t = riemannZetaSPath T (2 * t - 3) := by
  rw [rectBoundary_of_mem_Icc_two_three ⟨ht.1, by linarith [ht.2]⟩,
    riemannZetaSPath_of_one_le (by linarith [ht.1])]
  apply Complex.ext <;> simp <;> ring

lemma rb_half_three {t : ℝ} (ht : t ∈ Icc (5 / 2 : ℝ) 3) :
    rectBoundary (-1 : ℂ) (2 + T * I) t = 1 - conj (riemannZetaSPath T (7 - 2 * t)) := by
  have e : riemannZetaSPath T (7 - 2 * t) = ((2 - 3 / 2 * (7 - 2 * t - 1) : ℝ) : ℂ) + T * I := by
    rw [riemannZetaSPath_of_one_le (by linarith [ht.2])]; push_cast; ring
  rw [rectBoundary_of_mem_Icc_two_three ⟨by linarith [ht.1], ht.2⟩, e, map_add, conj_ofReal,
    map_mul, conj_ofReal, conj_I]
  apply Complex.ext <;> simp <;> ring

lemma rb_three_four {t : ℝ} (ht : t ∈ Icc (3 : ℝ) 4) :
    rectBoundary (-1 : ℂ) (2 + T * I) t = 1 - conj (riemannZetaSPath T (4 - t)) := by
  have e : riemannZetaSPath T (4 - t) = ((2 : ℝ) : ℂ) + ((4 - t) * T : ℝ) * I := by
    rw [riemannZetaSPath_of_le_one (by linarith [ht.1])]; push_cast; ring
  rw [rectBoundary_of_mem_Icc_three_four ht, e, map_add, conj_ofReal, map_mul, conj_ofReal, conj_I]
  apply Complex.ext <;> simp <;> ring

/-- **(C).** The Riemann-von Mangoldt identity: for `T ≥ 14` not an ordinate,
`N(T) = θ(T)/π + 1 + S(T)` with `rsTheta` of `SchoenfeldS1.B` (the continuous branch,
`rsTheta 0 = 0`) and `S(T) = riemannZetaS T` of Tau Ceti. -/
theorem NT_eq_rsTheta_add (hT : 14 ≤ T) (hord : NotOrdinate T) :
    (NT T : ℝ) = rsTheta T / π + 1 + riemannZetaS T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨Θ, hΘc, hΘl, hΘ0, hΘ2⟩ := exists_arg_xi_path hT hord
  obtain ⟨θ, hθc, hθl⟩ := exists_continuousOn_eq_norm_mul_exp_rectBoundary (f := xi) (z := -1)
    (w := 2 + T * I) continuous_xi.continuousOn (xi_ne_zero_frontier hord)
  have hmain := rect_arg_sub_eq_two_pi_mul_NT hT0 hord hθc hθl
  -- bottom cell: argument 0
  have c0 : θ 1 - θ 0 = 0 := by
    have := cell_var hord (ψ := fun _ => 0) (a := 0) (b := 1) (by norm_num)
      (Icc_subset_Icc le_rfl (by norm_num)) hθc hθl continuousOn_const
      (fun t ht => by rw [rb_zero_one ht]; exact polar_ofReal_pos _)
    simpa using this
  -- right cell: argument Θ (t - 1)
  have c1 : θ 2 - θ 1 = Θ 1 := by
    have hψ : ContinuousOn (fun t : ℝ => Θ (t - 1)) (Icc 1 2) :=
      hΘc.comp (by fun_prop) fun t ht => (by constructor <;> linarith [ht.1, ht.2])
    have := cell_var hord (ψ := fun t => Θ (t - 1)) (a := 1) (b := 2) (by norm_num)
      (Icc_subset_Icc (by norm_num) (by norm_num)) hθc hθl hψ
      (fun t ht => by rw [rb_one_two ht]; exact hΘl _ (by constructor <;> linarith [ht.1, ht.2]))
    rw [this]; norm_num [hΘ0]
  -- top-right cell: argument Θ (2t - 3)
  have c2 : θ (5 / 2) - θ 2 = Θ 2 - Θ 1 := by
    have hψ : ContinuousOn (fun t : ℝ => Θ (2 * t - 3)) (Icc 2 (5 / 2)) :=
      hΘc.comp (by fun_prop) fun t ht => (by constructor <;> linarith [ht.1, ht.2])
    have := cell_var hord (ψ := fun t => Θ (2 * t - 3)) (a := 2) (b := 5 / 2) (by norm_num)
      (Icc_subset_Icc (by norm_num) (by norm_num)) hθc hθl hψ
      (fun t ht => by rw [rb_two_half ht]; exact hΘl _ (by constructor <;> linarith [ht.1, ht.2]))
    rw [this]; norm_num
  -- top-left cell: argument -Θ (7 - 2t)
  have c3 : θ 3 - θ (5 / 2) = Θ 2 - Θ 1 := by
    have hψ : ContinuousOn (fun t : ℝ => -Θ (7 - 2 * t)) (Icc (5 / 2) 3) :=
      (hΘc.comp (by fun_prop) fun t ht => (by constructor <;> linarith [ht.1, ht.2])).neg
    have := cell_var hord (ψ := fun t => -Θ (7 - 2 * t)) (a := 5 / 2) (b := 3) (by norm_num)
      (Icc_subset_Icc (by norm_num) (by norm_num)) hθc hθl hψ
      (fun t ht => by
        rw [rb_half_three ht, xi_one_sub, xi_conj]
        exact polar_conj (hΘl _ (by constructor <;> linarith [ht.1, ht.2])))
    rw [this]; norm_num; ring
  -- left cell: argument -Θ (4 - t)
  have c4 : θ 4 - θ 3 = Θ 1 := by
    have hψ : ContinuousOn (fun t : ℝ => -Θ (4 - t)) (Icc 3 4) :=
      (hΘc.comp (by fun_prop) fun t ht => (by constructor <;> linarith [ht.1, ht.2])).neg
    have := cell_var hord (ψ := fun t => -Θ (4 - t)) (a := 3) (b := 4) (by norm_num)
      (Icc_subset_Icc (by norm_num) le_rfl) hθc hθl hψ
      (fun t ht => by
        rw [rb_three_four ht, xi_one_sub, xi_conj]
        exact polar_conj (hΘl _ (by constructor <;> linarith [ht.1, ht.2])))
    rw [this]; norm_num [hΘ0]
  have htot : 2 * π * NT T = 2 * (π + rsTheta T + π * riemannZetaS T) := by
    rw [← hmain, ← hΘ2]; linarith
  have hpi := Real.pi_pos
  field_simp
  linarith
end SchoenfeldS1

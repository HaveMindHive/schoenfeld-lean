/-
Schoenfeld S1, part R: the argument principle for `xi` on the rectangle `[-1, 2] × [0, T]`:
any continuous argument of `xi` along its boundary changes by `2π N(T)`.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0; the Tau Ceti
rectangle argument principle is Apache-2.0 (The Tau Ceti contributors).
-/
import SchoenfeldS1.X
import SchoenfeldS1.D3
import TauCeti.Analysis.Contour.Argument.Rectangle.Basic
import TauCeti.Analysis.Contour.Argument.Rectangle.Variation

/-!
# `θ 4 - θ 0 = 2π N(T)` along the boundary of `[-1, 2] × [0, T]`

For `T > 0` not an ordinate, `xi` has no zero on the frontier of `R = Rectangle (-1) (2 + iT)`
(real axis: `xi_ofReal_ne_zero`; `Re = -1`, `Re = 2`: off the strip; `Im = T`:
`xi_ne_zero_of_notOrdinate`). Tau Ceti's `argumentPrinciple_rectBoundary_of_analyticOnNhd` on the
open rectangle `U = (-2, 3) × (-1, T + 1)` with the finite zero set `zerosBandF (-1) (T + 1)` gives
`∮ xi'/xi = 2πi Σ_{ρ ∈ R} ord_ρ xi`, the sum being `N(T)` (`analyticOrderNatAt_xi`), and the
contour integral is `i (θ 4 - θ 0)` for any continuous argument `θ` of `xi` along the boundary
(`integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub`).
-/

namespace SchoenfeldS1

open Complex Real Set TauCeti TauCeti.Contour
open scoped Classical

local notation "ζ" => riemannZeta

variable {T : ℝ}

lemma re_neg_one_le : (-1 : ℂ).re ≤ (2 + T * I).re := by simp; norm_num

lemma im_neg_one_le (hT : 0 < T) : (-1 : ℂ).im ≤ (2 + T * I).im := by simp; exact hT.le

/-- `xi` has no zero on the frontier of `[-1, 2] × [0, T]` when `T` is not an ordinate. -/
theorem xi_ne_zero_frontier (hord : NotOrdinate T) :
    ∀ x ∈ frontier (Rectangle (-1 : ℂ) (2 + T * I)), xi x ≠ 0 := by
  intro x hx
  rw [frontier_rectangle, mem_union, mem_reProdIm, mem_reProdIm] at hx
  simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im, zero_add,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with ⟨_, h0 | hT'⟩ | ⟨hm | h2, _⟩
  · have : x = ((x.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h0]
    rw [this]; exact xi_ofReal_ne_zero _
  · have : x = (x.re : ℂ) + T * I := by apply Complex.ext <;> simp [hT']
    rw [this]; exact xi_ne_zero_of_notOrdinate hord _
  · exact xi_ne_zero_of_re_nonpos (by rw [hm]; norm_num)
  · exact xi_ne_zero_of_one_le_re (by rw [h2]; norm_num)

/-- The zeros of `xi` in the rectangle `[-1, 2] × [0, T]` are the zeros of `ζ` counted by `N(T)`. -/
theorem filter_zerosBandF_eq (hT : 0 < T) :
    (zerosBandF (-1) (T + 1)).filter (· ∈ Rectangle (-1 : ℂ) (2 + T * I)) = zerosBandF 0 T := by
  ext ρ
  rw [Finset.mem_filter, mem_zerosBandF, mem_zerosBandF,
    mem_rectangle_iff re_neg_one_le (im_neg_one_le hT)]
  simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im, zero_add]
  constructor
  · rintro ⟨⟨hz, h0, h1, -, -⟩, -, h0i, hi⟩
    exact ⟨hz, h0, h1, lt_of_le_of_ne h0i (im_ne_zero_of_zero hz h0 h1).symm, hi⟩
  · rintro ⟨hz, h0, h1, h0i, hi⟩
    exact ⟨⟨hz, h0, h1, by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, h0i.le, hi⟩

/-- The order sum of `xi` over the rectangle is `N(T)`. -/
theorem sum_order_xi_eq_NT (hT : 0 < T) :
    ∑ s ∈ zerosBandF (-1) (T + 1) with s ∈ Rectangle (-1 : ℂ) (2 + T * I),
      (analyticOrderNatAt xi s : ℂ) = (NT T : ℂ) := by
  rw [filter_zerosBandF_eq hT]
  unfold NT Nband
  push_cast
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨-, h0, h1, -, -⟩ := mem_zerosBandF.mp hρ
  rw [analyticOrderNatAt_xi h0 h1]

/-- **The argument principle for `xi` on `[-1, 2] × [0, T]`.** For `T > 0` not an ordinate, any
continuous argument `θ` of `xi` along `rectBoundary (-1) (2 + iT)` on `[0, 4]` changes by
`2π N(T)`. -/
theorem rect_arg_sub_eq_two_pi_mul_NT (hT : 0 < T) (hord : NotOrdinate T) {θ : ℝ → ℝ}
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 4, xi (rectBoundary (-1 : ℂ) (2 + T * I) t) =
      ‖xi (rectBoundary (-1 : ℂ) (2 + T * I) t)‖ * exp (I * θ t)) :
    θ 4 - θ 0 = 2 * π * NT T := by
  set U : Set ℂ := Ioo (-2 : ℝ) 3 ×ℂ Ioo (-1 : ℝ) (T + 1) with hUdef
  have hU : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hre := @re_neg_one_le T
  have him := im_neg_one_le hT
  have hRU : Rectangle (-1 : ℂ) (2 + T * I) ⊆ U := by
    intro x hx
    rw [mem_rectangle_iff hre him] at hx
    rw [hUdef, mem_reProdIm, mem_Ioo, mem_Ioo]
    simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im,
      zero_add] at hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]
  have hzeros : ∀ x ∈ U, xi x = 0 → x ∈ zerosBandF (-1) (T + 1) := by
    intro x hx h
    obtain ⟨h0, h1⟩ := re_pos_lt_one_of_xi_eq_zero h
    rw [hUdef, mem_reProdIm, mem_Ioo, mem_Ioo] at hx
    rw [mem_zerosBandF]
    exact ⟨(xi_eq_zero_iff h0 h1).mp h, h0, h1, hx.2.1, hx.2.2.le⟩
  have hfr := xi_ne_zero_frontier hord
  have hAP := argumentPrinciple_rectBoundary_of_analyticOnNhd hre him hU hRU
    (analyticOnNhd_xi.mono (subset_univ _)) hzeros hfr
  rw [sum_order_xi_eq_NT hT] at hAP
  have hu : uIcc (0 : ℝ) 4 = Icc 0 4 := uIcc_of_le (by norm_num)
  have hint := AbsolutelyContinuousOnInterval.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub
    (isPiecewiseC1On_rectBoundary (-1 : ℂ) (2 + T * I)).absolutelyContinuousOnInterval
    (fun t _ => analyticAt_xi _) (fun t _ => hfr _ (rectBoundary_mem_frontier t)) (hu ▸ hθ)
    (hu ▸ hlift)
  rw [hAP, rectBoundary_four, rectBoundary_zero, sub_self, ofReal_zero, zero_add] at hint
  have h : I * ((θ 4 - θ 0 : ℝ) : ℂ) = I * ((2 * π * NT T : ℝ) : ℂ) := by
    rw [← hint]
    push_cast
    ring
  exact_mod_cast mul_left_cancel₀ I_ne_zero h

end SchoenfeldS1

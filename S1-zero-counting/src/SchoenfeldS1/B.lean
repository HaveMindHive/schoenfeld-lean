/-
Schoenfeld S1, part B: explicit Stirling for the Riemann-Siegel theta function.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against Mathlib 31ce06ea
and Tau Ceti (riemann-hypothesis-community repository, Lean v4.37.0-rc1). Apache-2.0.
Uses Tau Ceti's `logGamma` and Nemes's explicit Stirling remainder bound
`TauCeti.norm_stirlingRemainder_le` (TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Basic.lean).
-/
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic

/-!
# The Riemann-Siegel theta function with an explicit Stirling error

`rsTheta T = Im logΓ(1/4 + iT/2) - (T/2) log π` (continuous branch, `rsTheta 0 = 0`), and
`rsThetaMain T = (T/2) log (T/(2π)) - T/2 - π/8`.

Main result: `abs_rsTheta_sub_main_le`: for `T > 0`,
`|rsTheta T - rsThetaMain T| ≤ 11 / (16 T)`.

The three pieces of the error are `(T/2)(log ‖z‖ - log (T/2)) ∈ [0, 1/(16T)]`,
`(1/4) arctan (1/(2T)) ∈ [0, 1/(8T)]` and `Im (stirlingRemainder z)`, bounded by
`1/(8 cos²(arg z / 2) ‖z‖) ≤ 1/(2T)` since `0 ≤ arg z ≤ π/2` and `‖z‖ ≥ T/2`, where
`z = 1/4 + iT/2`. The classical value of the total is `1/(48T) + O(T⁻³)`; the bound here is coarser
but fully explicit.
-/

namespace SchoenfeldS1

open Complex Real

/-- The point `z = 1/4 + iT/2`. -/
noncomputable def zTheta (T : ℝ) : ℂ := ⟨1 / 4, T / 2⟩

/-- The Riemann-Siegel theta function, `Im logΓ(1/4 + iT/2) - (T/2) log π`. -/
noncomputable def rsTheta (T : ℝ) : ℝ := (TauCeti.logGamma (zTheta T)).im - T / 2 * Real.log π

/-- The Stirling main term of `rsTheta`, `(T/2) log (T/(2π)) - T/2 - π/8`. -/
noncomputable def rsThetaMain (T : ℝ) : ℝ := T / 2 * Real.log (T / (2 * π)) - T / 2 - π / 8

@[simp] lemma zTheta_re (T : ℝ) : (zTheta T).re = 1 / 4 := rfl
@[simp] lemma zTheta_im (T : ℝ) : (zTheta T).im = T / 2 := rfl

lemma zTheta_mem_slitPlane (T : ℝ) : zTheta T ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; rw [zTheta_re]; norm_num

lemma norm_zTheta_sq (T : ℝ) : ‖zTheta T‖ ^ 2 = 1 / 16 + T ^ 2 / 4 := by
  rw [Complex.sq_norm, zTheta, Complex.normSq_mk]; ring

lemma half_le_norm_zTheta {T : ℝ} (hT : 0 < T) : T / 2 ≤ ‖zTheta T‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), Real.le_sqrt (by positivity) (by positivity),
    norm_zTheta_sq]
  nlinarith

lemma norm_zTheta_le {T : ℝ} (hT : 0 < T) : ‖zTheta T‖ ≤ T / 2 + 1 / (16 * T) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [norm_zTheta_sq]
  have h : (T / 2 + 1 / (16 * T)) ^ 2 = T ^ 2 / 4 + 1 / 16 + 1 / (256 * T ^ 2) := by
    field_simp; ring
  rw [h]
  have : 0 < 1 / (256 * T ^ 2) := by positivity
  linarith

lemma norm_zTheta_pos {T : ℝ} (hT : 0 < T) : 0 < ‖zTheta T‖ :=
  lt_of_lt_of_le (by positivity) (half_le_norm_zTheta hT)

lemma arg_zTheta {T : ℝ} (hT : 0 < T) : (zTheta T).arg = π / 2 - Real.arctan (1 / (2 * T)) := by
  rw [Complex.arg_eq_pi_div_two_sub_arctan_of_im_pos (by rw [zTheta_im]; positivity), zTheta_re,
    zTheta_im]
  have : (1 / 4 : ℝ) / (T / 2) = 1 / (2 * T) := by field_simp; norm_num
  rw [this]

lemma arg_zTheta_nonneg {T : ℝ} (hT : 0 < T) : 0 ≤ (zTheta T).arg :=
  Complex.arg_nonneg_iff.mpr (by rw [zTheta_im]; positivity)

lemma arg_zTheta_le (T : ℝ) : (zTheta T).arg ≤ π / 2 :=
  Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by rw [zTheta_re]; norm_num))

/-- `log ‖z‖ - log (T/2) ∈ [0, 1/(8T²)]`. -/
lemma log_norm_zTheta_sub_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ Real.log ‖zTheta T‖ - Real.log (T / 2) ∧
      Real.log ‖zTheta T‖ - Real.log (T / 2) ≤ 1 / (8 * T ^ 2) := by
  have hz := norm_zTheta_pos hT
  have hT2 : 0 < T / 2 := by positivity
  constructor
  · linarith [Real.log_le_log hT2 (half_le_norm_zTheta hT)]
  · rw [← Real.log_div hz.ne' hT2.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hz hT2)
    have h2 : ‖zTheta T‖ / (T / 2) - 1 ≤ 1 / (8 * T ^ 2) := by
      rw [div_sub_one hT2.ne', div_le_div_iff₀ hT2 (by positivity)]
      have := norm_zTheta_le hT
      have e : (T / 2 + 1 / (16 * T) - T / 2) * (8 * T ^ 2) = T / 2 := by field_simp; ring
      nlinarith
    linarith

/-- `arctan (1/(2T)) ∈ [0, 1/(2T)]`. -/
lemma arctan_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ Real.arctan (1 / (2 * T)) ∧ Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) :=
  ⟨Real.arctan_nonneg.mpr (by positivity), Real.arctan_le_self (by positivity)⟩

/-- `|Im (stirlingRemainder z)| ≤ 1/(2T)`. -/
lemma abs_im_stirlingRemainder_zTheta_le {T : ℝ} (hT : 0 < T) :
    |(TauCeti.stirlingRemainder (zTheta T)).im| ≤ 1 / (2 * T) := by
  have hz := norm_zTheta_pos hT
  refine (Complex.abs_im_le_norm _).trans ((TauCeti.norm_stirlingRemainder_le
    (zTheta_mem_slitPlane T)).trans ?_)
  -- `cos (arg z / 2) ≥ cos (π/4) = √2/2`, so `cos² ≥ 1/2`
  have hc : Real.cos (π / 4) ≤ Real.cos ((zTheta T).arg / 2) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · linarith [arg_zTheta_nonneg hT]
    · linarith [Real.pi_pos]
    · linarith [arg_zTheta_le T]
  rw [Real.cos_pi_div_four] at hc
  have hs : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hc2 : 1 / 2 ≤ Real.cos ((zTheta T).arg / 2) ^ 2 := by
    rw [← hs]
    exact pow_le_pow_left₀ (by positivity) hc 2
  have hn := half_le_norm_zTheta hT
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- `rsTheta` expanded through Stirling's formula. -/
lemma rsTheta_eq (T : ℝ) :
    rsTheta T = T / 2 * Real.log ‖zTheta T‖ - 1 / 4 * (zTheta T).arg - T / 2
      + (TauCeti.stirlingRemainder (zTheta T)).im - T / 2 * Real.log π := by
  unfold rsTheta
  rw [TauCeti.logGamma_eq_add_stirlingRemainder]
  have h1 : (zTheta T - 1 / 2).re = -1 / 4 := by simp [zTheta]; norm_num
  have h2 : (zTheta T - 1 / 2).im = T / 2 := by simp [zTheta]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.log_re,
    Complex.log_im, h1, h2, zTheta_im]
  ring

/-- **Explicit Stirling for the Riemann-Siegel theta**: for `T > 0`,
`|rsTheta T - ((T/2) log (T/(2π)) - T/2 - π/8)| ≤ 11/(16T)`. -/
theorem abs_rsTheta_sub_main_le {T : ℝ} (hT : 0 < T) :
    |rsTheta T - rsThetaMain T| ≤ 11 / (16 * T) := by
  have hT2 : 0 < T / 2 := by positivity
  have hlog : Real.log (T / (2 * π)) = Real.log (T / 2) - Real.log π := by
    rw [← Real.log_div hT2.ne' Real.pi_pos.ne']; congr 1; field_simp
  obtain ⟨hl0, hl1⟩ := log_norm_zTheta_sub_bounds hT
  obtain ⟨ha0, ha1⟩ := arctan_bounds hT
  have hR := abs_im_stirlingRemainder_zTheta_le hT
  rw [rsTheta_eq, rsThetaMain, hlog, arg_zTheta hT]
  set L := Real.log ‖zTheta T‖ - Real.log (T / 2) with hL
  set A := Real.arctan (1 / (2 * T)) with hA
  set R := (TauCeti.stirlingRemainder (zTheta T)).im with hR'
  have e : T / 2 * Real.log ‖zTheta T‖ - 1 / 4 * (π / 2 - A) - T / 2 + R - T / 2 * Real.log π
      - (T / 2 * (Real.log (T / 2) - Real.log π) - T / 2 - π / 8) = T / 2 * L + 1 / 4 * A + R := by
    rw [hL]; ring
  rw [e]
  have hTL0 : 0 ≤ T / 2 * L := mul_nonneg hT2.le hl0
  have hTL1 : T / 2 * L ≤ 1 / (16 * T) := by
    calc T / 2 * L ≤ T / 2 * (1 / (8 * T ^ 2)) := mul_le_mul_of_nonneg_left hl1 hT2.le
      _ = 1 / (16 * T) := by field_simp; ring
  have hA1 : 1 / 4 * A ≤ 1 / (8 * T) := by
    calc 1 / 4 * A ≤ 1 / 4 * (1 / (2 * T)) := mul_le_mul_of_nonneg_left ha1 (by norm_num)
      _ = 1 / (8 * T) := by field_simp; ring
  have hA0 : 0 ≤ 1 / 4 * A := by positivity
  have hsum : 1 / (16 * T) + 1 / (8 * T) + 1 / (2 * T) = 11 / (16 * T) := by field_simp; ring
  rw [abs_le] at hR ⊢
  constructor
  · have : 0 ≤ 1 / (16 * T) + 1 / (8 * T) := by positivity
    linarith [hR.1]
  · linarith [hR.2]

/-- For `T ≥ 14` the Stirling error of `rsTheta` is at most `11/224 < 0.05`. -/
theorem abs_rsTheta_sub_main_le_of_fourteen_le {T : ℝ} (hT : 14 ≤ T) :
    |rsTheta T - rsThetaMain T| ≤ 11 / 224 := by
  have hT0 : 0 < T := by linarith
  refine (abs_rsTheta_sub_main_le hT0).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `rsTheta 0 = 0`: `logΓ(1/4)` is real. -/
theorem rsTheta_zero : rsTheta 0 = 0 := by
  unfold rsTheta
  have h : zTheta 0 = ((1 / 4 : ℝ) : ℂ) := by apply Complex.ext <;> simp [zTheta]
  rw [h]
  have : (TauCeti.logGamma ((1 / 4 : ℝ) : ℂ)).im = 0 := by
    rw [TauCeti.logGamma_eq_add_stirlingRemainder]
    have hR := TauCeti.stirlingRemainder_ofReal_im (by norm_num : (0 : ℝ) < 1 / 4)
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, hR]
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg (by norm_num)]
    simp
  rw [this]; simp

end SchoenfeldS1

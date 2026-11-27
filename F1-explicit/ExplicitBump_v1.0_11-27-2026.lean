import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.MellinTransform.SmoothCutoff

/-!
# An explicit bump for the smoothed cutoff (11-27-2026)

Tau Ceti's `exists_norm_mellin_smoothCutoff_le` gives
`‖𝓜χ_ε(s)‖ ≤ C / (|s| (1 + ε|s|))` with an existential `C` (by compactness). Here the bump is
explicit, `ν = ν₀ / m₀` with `ν₀ x = (max 0 ((x - 1/2)(2 - x)))^2`, and the constant is the
numeral `168`.

Constants. On `[1/2, 2]`: `0 ≤ ν₀ ≤ 81/256`, `|ν₀'| ≤ 27/16`; for `0 < Re w ≤ 2`:
`|x^(w-1)| ≤ 8`, `|x^w| ≤ 4`. The interval has length `3/2`. So
`‖𝓜ν₀(w)‖ ≤ 8 · 81/256 · 3/2 = 243/64` and, integrating by parts (boundary terms vanish),
`‖w‖ ‖𝓜ν₀(w)‖ ≤ 4 · 27/16 · 3/2 = 81/8`, hence `(1 + ‖w‖) ‖𝓜ν₀(w)‖ ≤ 891/64`. The mass
`m₀ = ∫ ν₀/x ≥ 1/12` (on `[1, 3/2]`, `ν₀/x ≥ 1/6`), so `(1 + ‖w‖) ‖𝓜ν(w)‖ ≤ 891·12/64 < 168`.
With `w = εs` and `𝓜χ_ε(s) = 𝓜ν(εs)/s` (Tau Ceti `mellin_smoothCutoff`) the bound follows.
-/

open Set MeasureTheory Complex Filter Asymptotics
open scoped Topology Interval

namespace WallsMeetRHExplicit

/-- The quadratic `p x = (x - 1/2)(2 - x)`, positive exactly on `(1/2, 2)`. -/
noncomputable def bump_p (x : ℝ) : ℝ := (x - 1 / 2) * (2 - x)

/-- `h y = (max 0 y)^2`, of class `C^1` with derivative `2 max 0 y`. -/
noncomputable def bump_h (y : ℝ) : ℝ := (max 0 y) ^ 2

/-- The unnormalized bump `ν₀ = h ∘ p`. -/
noncomputable def bump_nu0 (x : ℝ) : ℝ := bump_h (bump_p x)

/-- Its derivative. -/
noncomputable def bump_dnu0 (x : ℝ) : ℝ := 2 * max 0 (bump_p x) * (5 / 2 - 2 * x)

lemma bump_p_hasDerivAt (x : ℝ) : HasDerivAt bump_p (5 / 2 - 2 * x) x := by
  have := ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).mul ((hasDerivAt_id x).const_sub (2 : ℝ))
  convert this using 1
  · funext t; simp [bump_p]
  · simp; ring

lemma bump_h_hasDerivAt (y : ℝ) : HasDerivAt bump_h (2 * max 0 y) y := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have he : bump_h =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      simp [bump_h, max_eq_left (show z < 0 from hz).le]
    rw [max_eq_left hy.le, mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq he
  · rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have hb : (fun t : ℝ ↦ bump_h (0 + t) - bump_h 0 - t • (0 : ℝ)) =O[𝓝 0]
        fun t : ℝ ↦ t ^ 2 := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
      simp only [bump_h, zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sub_zero, smul_zero, Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      rcases le_total t 0 with ht | ht
      · rw [max_eq_left ht]; nlinarith [sq_nonneg t]
      · rw [max_eq_right ht]
    exact hb.trans_isLittleO (isLittleO_pow_id (by norm_num))
  · have he : bump_h =ᶠ[𝓝 y] fun z ↦ z ^ 2 := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      simp [bump_h, max_eq_right (show 0 < z from hz).le]
    rw [max_eq_right hy.le]
    have := (hasDerivAt_pow 2 y).congr_of_eventuallyEq he
    norm_num at this
    exact this

lemma bump_nu0_hasDerivAt (x : ℝ) : HasDerivAt bump_nu0 (bump_dnu0 x) x := by
  have := (bump_h_hasDerivAt (bump_p x)).comp x (bump_p_hasDerivAt x)
  convert this using 1 <;> rfl

lemma bump_continuous_dnu0 : Continuous bump_dnu0 := by
  unfold bump_dnu0 bump_p; fun_prop

lemma bump_contDiff : ContDiff ℝ 1 bump_nu0 := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (bump_nu0_hasDerivAt x).differentiableAt, ?_⟩
  have : deriv bump_nu0 = bump_dnu0 := funext fun x ↦ (bump_nu0_hasDerivAt x).deriv
  rw [this]; exact bump_continuous_dnu0

lemma bump_p_le (x : ℝ) : bump_p x ≤ 9 / 16 := by
  unfold bump_p; nlinarith [sq_nonneg (x - 5 / 4)]

lemma bump_p_nonpos {x : ℝ} (h : x ≤ 1 / 2 ∨ 2 ≤ x) : bump_p x ≤ 0 := by
  unfold bump_p
  rcases h with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

lemma bump_nu0_eq_zero {x : ℝ} (h : x ≤ 1 / 2 ∨ 2 ≤ x) : bump_nu0 x = 0 := by
  simp [bump_nu0, bump_h, max_eq_left (bump_p_nonpos h)]

lemma bump_nu0_nonneg (x : ℝ) : 0 ≤ bump_nu0 x := sq_nonneg _

lemma bump_nu0_le (x : ℝ) : bump_nu0 x ≤ 81 / 256 := by
  have h1 : 0 ≤ max 0 (bump_p x) := le_max_left _ _
  have h2 : max 0 (bump_p x) ≤ 9 / 16 := max_le (by norm_num) (bump_p_le x)
  unfold bump_nu0 bump_h; nlinarith

lemma bump_abs_dnu0_le {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) : |bump_dnu0 x| ≤ 27 / 16 := by
  have h1 : 0 ≤ max 0 (bump_p x) := le_max_left _ _
  have h2 : max 0 (bump_p x) ≤ 9 / 16 := max_le (by norm_num) (bump_p_le x)
  have h3 : |5 / 2 - 2 * x| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  unfold bump_dnu0
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_two]
  have := abs_nonneg (5 / 2 - 2 * x)
  nlinarith

lemma bump_rpow_le {x σ : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    x ^ σ ≤ 4 :=
  calc x ^ σ ≤ 2 ^ σ := Real.rpow_le_rpow hx0.le hx2 hσ0
    _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
    _ = 4 := by norm_num

/-- `ν₀` vanishes on `(0, ∞)` off `(1/2, 2]`, so its Mellin transform is an integral over
`[1/2, 2]`. -/
lemma bump_mellin_eq (w : ℂ) :
    mellin (fun x ↦ (bump_nu0 x : ℂ)) w =
      ∫ x in (1 / 2 : ℝ)..2, (x : ℂ) ^ (w - 1) * bump_nu0 x := by
  have hsub : Ioc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx ↦ (by norm_num : (0 : ℝ) < 1 / 2).trans hx.1
  rw [intervalIntegral.integral_of_le (by norm_num), mellin,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub]
  · simp only [smul_eq_mul]
  · intro x hx
    have : x ≤ 1 / 2 ∨ 2 ≤ x := by
      by_contra h
      push Not at h
      exact hx.2 ⟨h.1, h.2.le⟩
    simp [bump_nu0_eq_zero this]

/-- Integration by parts on `[1/2, 2]`; the boundary terms vanish since `ν₀(1/2) = ν₀(2) = 0`. -/
lemma bump_ibp {w : ℂ} (hw : 0 < w.re) :
    w * ∫ x in (1 / 2 : ℝ)..2, (x : ℂ) ^ (w - 1) * bump_nu0 x =
      -∫ x in (1 / 2 : ℝ)..2, (bump_dnu0 x : ℂ) * (x : ℂ) ^ w := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hpos : ∀ x ∈ [[(1 / 2 : ℝ), 2]], 0 < x := fun x hx ↦ by
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x ↦ (bump_nu0 x : ℂ)) (u' := fun x ↦ (bump_dnu0 x : ℂ))
    (v := fun x : ℝ ↦ (x : ℂ) ^ w) (v' := fun x : ℝ ↦ w * (x : ℂ) ^ (w - 1))
    (a := 1 / 2) (b := 2)
    (fun x _ ↦ (bump_nu0_hasDerivAt x).ofReal_comp)
    (fun x hx ↦ hasDerivAt_ofReal_cpow_const (hpos x hx).ne' hw0)
    ((continuous_ofReal.comp bump_continuous_dnu0).intervalIntegrable _ _)
    (ContinuousOn.intervalIntegrable fun x hx ↦ (continuousAt_const.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne'))).continuousWithinAt)
  rw [bump_nu0_eq_zero (Or.inr le_rfl), bump_nu0_eq_zero (Or.inl le_rfl)] at h
  simp only [ofReal_zero, zero_mul, sub_zero, zero_sub] at h
  rw [← intervalIntegral.integral_const_mul, ← h]
  congr 1
  funext x
  ring

/-- `‖𝓜ν₀(w)‖ ≤ 8 · 81/256 · 3/2 = 243/64` for `0 < Re w ≤ 2`. -/
lemma bump_norm_mellin_le {w : ℂ} (hw0 : 0 < w.re) (hw2 : w.re ≤ 2) :
    ‖mellin (fun x ↦ (bump_nu0 x : ℂ)) w‖ ≤ 243 / 64 := by
  rw [bump_mellin_eq]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 8 * (81 / 256))
    fun x hx ↦ ?_).trans (le_of_eq (by norm_num))
  rw [uIoc_of_le (by norm_num)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bump_nu0_nonneg x)]
  have hre : (w - 1).re = w.re - 1 := by simp
  rw [hre, Real.rpow_sub_one hx0.ne']
  have h4 := bump_rpow_le hx0 hx.2 hw0.le hw2
  have h8 : x ^ w.re / x ≤ 8 := by
    rw [div_le_iff₀ hx0]
    linarith [hx.1]
  exact mul_le_mul h8 (bump_nu0_le x) (bump_nu0_nonneg x) (by norm_num)

/-- `‖w‖ ‖𝓜ν₀(w)‖ ≤ 27/16 · 4 · 3/2 = 81/8` for `0 < Re w ≤ 2`. -/
lemma bump_norm_mul_mellin_le {w : ℂ} (hw0 : 0 < w.re) (hw2 : w.re ≤ 2) :
    ‖w‖ * ‖mellin (fun x ↦ (bump_nu0 x : ℂ)) w‖ ≤ 81 / 8 := by
  rw [← norm_mul, bump_mellin_eq, bump_ibp hw0, norm_neg]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 27 / 16 * 4)
    fun x hx ↦ ?_).trans (le_of_eq (by norm_num))
  rw [uIoc_of_le (by norm_num)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (bump_abs_dnu0_le ⟨hx.1.le, hx.2⟩) (bump_rpow_le hx0 hx.2 hw0.le hw2)
    (by positivity) (by norm_num)

lemma bump_combined {w : ℂ} (hw0 : 0 < w.re) (hw2 : w.re ≤ 2) :
    ‖mellin (fun x ↦ (bump_nu0 x : ℂ)) w‖ * (1 + ‖w‖) ≤ 891 / 64 := by
  have ha := bump_norm_mellin_le hw0 hw2
  have hb := bump_norm_mul_mellin_le hw0 hw2
  nlinarith

/-- The mass of `ν₀` against `dx/x`. -/
noncomputable def bump_m0 : ℝ := ∫ x in Ioi 0, bump_nu0 x / x

lemma bump_support : Function.support bump_nu0 ∩ Ioi 0 ⊆ Icc (1 / 2) 2 := fun x hx ↦ by
  by_contra h
  have : x ≤ 1 / 2 ∨ 2 ≤ x := by
    simp only [mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · left; linarith
    · right; linarith
  exact hx.1 (bump_nu0_eq_zero this)

lemma bump_integrable : IntegrableOn (fun x ↦ bump_nu0 x / x) (Ioi 0) :=
  TauCeti.integrableOn_div_of_continuousOn_of_support_subset
    bump_contDiff.continuous.continuousOn bump_support

lemma bump_m0_ge : 1 / 12 ≤ bump_m0 := by
  have hsub : Icc (1 : ℝ) (3 / 2) ⊆ Ioi 0 := fun x hx ↦ by
    simp only [mem_Ioi]; linarith [hx.1]
  have h1 := setIntegral_mono_set (μ := volume) bump_integrable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx ↦
      div_nonneg (bump_nu0_nonneg x) (le_of_lt hx)) (ae_of_all _ hsub)
  have h2 := setIntegral_ge_of_const_le (c := (1 / 6 : ℝ)) (μ := volume) measurableSet_Icc
    (by simp) (fun x hx ↦ ?_) (bump_integrable.mono_set hsub)
  · rw [Real.volume_real_Icc, smul_eq_mul] at h2
    unfold bump_m0
    norm_num at h2 ⊢
    linarith
  · have hx0 : 0 < x := by linarith [hx.1]
    have hp : 1 / 2 ≤ bump_p x := by
      unfold bump_p
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
    have hn : 1 / 4 ≤ bump_nu0 x := by
      unfold bump_nu0 bump_h
      rw [max_eq_right (by linarith)]
      nlinarith
    rw [le_div_iff₀ hx0]
    linarith [hx.2]

/-- **The explicit bump.** `ν = ν₀ / m₀` with `ν₀ x = (max 0 ((x - 1/2)(2 - x)))^2` gives
`‖𝓜χ_ε(s)‖ ≤ 168 / (|s| (1 + ε|s|))` on `1/4 ≤ Re s ≤ 2`, `0 < ε ≤ 1`. -/
theorem exists_explicit_bump :
    ∃ ν : ℝ → ℝ, ContDiffOn ℝ 1 ν (Set.Ioi 0) ∧ (∀ y > 0, 0 ≤ ν y) ∧
      Function.support ν ∩ Set.Ioi 0 ⊆ Set.Icc (1 / 2) 2 ∧
      (∫ x in Set.Ioi 0, ν x / x) = 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 →
        ‖mellin (fun x ↦ (TauCeti.smoothCutoff ν ε x : ℂ)) s‖ ≤
          168 / (‖s‖ * (1 + ε * ‖s‖)) := by
  have hm0 : 0 < bump_m0 := lt_of_lt_of_le (by norm_num) bump_m0_ge
  set ν : ℝ → ℝ := fun x ↦ bump_nu0 x / bump_m0 with hν
  have hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2 := fun x hx ↦
    bump_support ⟨fun h ↦ hx.1 (by simp [hν, h]), hx.2⟩
  have hνc : Continuous ν := bump_contDiff.continuous.div_const _
  have hνi := TauCeti.integrableOn_div_of_continuousOn_of_support_subset hνc.continuousOn hνs
  refine ⟨ν, (bump_contDiff.div_const _).contDiffOn,
    fun y _ ↦ div_nonneg (bump_nu0_nonneg y) hm0.le, hνs, ?_, ?_⟩
  · have : ∀ x, ν x / x = bump_nu0 x / x / bump_m0 := fun x ↦ by simp only [hν]; ring
    simp_rw [this]
    rw [integral_div]
    exact div_self hm0.ne'
  · intro ε hε hε1 s hs1 hs2
    have hs0 : 0 < s.re := by linarith
    have hsn : 0 < ‖s‖ := hs0.trans_le (re_le_norm s)
    rw [TauCeti.mellin_smoothCutoff hνs hνi hε hs0, norm_div,
      div_le_div_iff₀ hsn (by positivity)]
    have hmel : mellin (fun x ↦ (ν x : ℂ)) (ε * s) =
        mellin (fun x ↦ (bump_nu0 x : ℂ)) (ε * s) / bump_m0 := by
      rw [← mellin_div_const]
      congr 1
      funext x
      simp [hν]
    have hre : ((ε : ℂ) * s).re = ε * s.re := re_ofReal_mul ε s
    have hn : ‖(ε : ℂ) * s‖ = ε * ‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have hc := bump_combined (w := ε * s) (by rw [hre]; positivity) (by rw [hre]; nlinarith)
    rw [hn] at hc
    rw [hmel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    set M := ‖mellin (fun x ↦ (bump_nu0 x : ℂ)) (ε * s)‖
    have hM : M * (1 + ε * ‖s‖) ≤ 168 * bump_m0 := by linarith [bump_m0_ge]
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    nlinarith [mul_le_mul_of_nonneg_left hM hsn.le]

end WallsMeetRHExplicit

#print axioms WallsMeetRHExplicit.exists_explicit_bump

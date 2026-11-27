import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Window
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Local
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Complex.JensenFormula
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import WallsMeetRHVonKoch

/-!
# Explicit constants for von Koch's bound from the proved RH (milestone F1, 11-27-2026)

Companion of `WallsMeetRHVonKoch_v1.0_11-27-2026.lean`, same environment (the locally built
community proof of RH by Alpöge with Claude, Mathlib `31ce06ea`, Tau Ceti pinned). The von Koch
file proves `|ψ(x) - x| ≤ C √x log² x` with an existential `C`; here every constant is a numeral.

The four existential inputs of the von Koch proof and their explicit replacements:
* the relative growth of `(s - 1) ζ(s)` on discs about `2 + it` (Tau Ceti: polynomial growth with
  an existential exponent): `norm_LFunctionTrivChar₁_one_le_pow_mul`, exponent `9`, on discs of
  radius `31/16`, which stay in `Re s ≥ 1/16` where Tau Ceti's explicit Euler–Maclaurin bound
  `‖ζ(s)‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` applies; the centre is bounded below by
  `‖ζ(2 + it)‖ > 1/2` (Möbius series);
* the unit-window zero count (Jensen): `count_zeros_disc_le`, `140 log(|t| + 2)` on discs of
  radius `29/16` about `2 + it`;
* the window form of `ζ′/ζ` (Landau's lemma): `logDeriv_window_explicit`, constant `33413`;
* the safe height and the sum `∑ m(ρ)/|ρ|`: `riemannZeta_safe_height_of` and
  `sum_order_div_norm_le_of`, parametrized by the two constants above;
* the Mellin transform of the smoothed cutoff: `exists_explicit_bump`, an explicit `C¹` bump.

Tau Ceti's `AnalyticOnNhd.sum_divisor_le_log_div_log` (Jensen) and
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le` (Landau) are already explicit in the growth
bound `M`; the work is to feed them explicit `M`. Private lemmas of Tau Ceti's `Window.lean` and
`Local.lean` are copied or adapted (Apache 2.0, copyright The Tau Ceti contributors).
-/

open Complex

namespace WallsMeetRHExplicit

/-! ## Copied from `WallsMeetRHVonKoch`: RH consequences, Tau Ceti private lemmas -/

/-- From the proved `riemannHypothesis`: `ζ(s) ≠ 0` for `Re s > 1/2`. -/
theorem riemannZeta_ne_zero_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro h0
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero h0
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := riemannHypothesis s h0 htriv hs1
  linarith

/-- From the proved `riemannHypothesis`: a zero of `ζ` in the strip `0 < Re ρ < 1` has
`Re ρ = 1/2`. -/
theorem re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

/-- Copy of a private lemma of Tau Ceti's `Window.lean` (Apache 2.0): a sum over the zeros of `ζ`
in a closed disc, as a `finsum` over a subtype, is the `Finset` sum over
`riemannZetaZerosClosedBall`. -/
theorem finsum_subtype_riemannZeta_eq_sum' {M : Type*} [AddCommMonoid M] (c : ℂ) (R : ℝ)
    (f : ℂ → M) :
    ∑ᶠ ρ : {z : ℂ // ‖z - c‖ ≤ R ∧ riemannZeta z = 0}, f ρ =
      ∑ z ∈ TauCeti.riemannZetaZerosClosedBall c R, f z := by
  rw [finsum_subtype_eq_finsum_cond (f := f)]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ TauCeti.mem_riemannZetaZerosClosedBall.symm

/-- Copy of a private lemma of Tau Ceti's `Window.lean` (Apache 2.0): the distance from `s` to
the point `2 + i Im s` of the line `Re = 2` is `|Re s - 2|`. -/
theorem norm_sub_two_add_im_mul_I (s : ℂ) : ‖s - (2 + s.im * I)‖ = |s.re - 2| := by
  have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-! ## Explicit relative growth of `(s - 1) ζ(s)` on discs about `2 + it` -/

/-- The centre lower bound: `‖(s₀ - 1) ζ(s₀)‖ ≥ 1/2` at `s₀ = 2 + it`, from `‖s₀ - 1‖ ≥ 1` and
the Möbius-series bound `‖ζ(s₀)‖⁻¹ < 1 + 1/(2 - 1) = 2`. -/
theorem one_half_le_norm_LFunctionTrivChar₁_one_two_add (t : ℝ) :
    1 / 2 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 (2 + t * I)‖ := by
  set s₀ : ℂ := 2 + t * I with hs₀
  have hre : s₀.re = 2 := by simp [s₀]
  have hs₀1 : s₀ ≠ 1 := fun h ↦ by rw [h, one_re] at hre; norm_num at hre
  rw [DirichletCharacter.LFunctionTrivChar₁_one_apply_of_ne_one hs₀1, norm_mul]
  have h1 : 1 ≤ ‖s₀ - 1‖ := by
    have := abs_re_le_norm (s₀ - 1)
    rw [sub_re, hre, one_re] at this
    norm_num at this
    exact this
  have hζ0 : riemannZeta s₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; norm_num)
  have hζ : 0 < ‖riemannZeta s₀‖ := norm_pos_iff.2 hζ0
  have h2 := TauCeti.inv_norm_riemannZeta_lt_one_add_one_div_sub_one (s := s₀) (by rw [hre]; norm_num)
  rw [hre] at h2
  norm_num at h2
  have h3 : 1 / 2 ≤ ‖riemannZeta s₀‖ := by
    rw [inv_lt_iff_one_lt_mul₀ hζ] at h2
    linarith
  calc (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
    _ ≤ ‖s₀ - 1‖ * ‖riemannZeta s₀‖ := mul_le_mul h1 h3 (by norm_num) (norm_nonneg _)

/-- **Explicit relative growth.** For `‖w - (2 + it)‖ ≤ 31/16` (so `Re w ≥ 1/16`),
`‖(w - 1) ζ(w)‖ ≤ (|t| + 2)^9 ‖(2 + it - 1) ζ(2 + it)‖`. From Tau Ceti's explicit right-half-plane
bound `‖ζ(w)‖ ≤ ‖w - 1‖⁻¹ + 1 + ‖w‖ / Re w`: `‖(w - 1) ζ(w)‖ ≤ 1 + (τ + 1)(1 + 16 (τ + 2)) ≤ 49 τ²`
with `τ = |t| + 2 ≥ 2`, and `49 τ² ≤ 98 τ² · (1/2) ≤ τ^9 ‖(s₀ - 1) ζ(s₀)‖`. -/
theorem norm_LFunctionTrivChar₁_one_le_pow_mul {t : ℝ} {w : ℂ} (hw : ‖w - (2 + t * I)‖ ≤ 31 / 16) :
    ‖DirichletCharacter.LFunctionTrivChar₁ 1 w‖ ≤
      (|t| + 2) ^ 9 * ‖DirichletCharacter.LFunctionTrivChar₁ 1 (2 + t * I)‖ := by
  set s₀ : ℂ := 2 + t * I with hs₀
  set τ : ℝ := |t| + 2 with hτ
  have hτ2 : 2 ≤ τ := by simp [τ]
  have hτ0 : 0 < τ := by linarith
  have hlow := one_half_le_norm_LFunctionTrivChar₁_one_two_add t
  -- `‖(w - 1) ζ(w)‖ ≤ 49 τ²`
  have hup : ‖DirichletCharacter.LFunctionTrivChar₁ 1 w‖ ≤ 49 * τ ^ 2 := by
    have hre : 1 / 16 ≤ w.re := by
      have := abs_re_le_norm (w - s₀)
      rw [sub_re, show s₀.re = 2 by simp [s₀]] at this
      have := (abs_le.1 (this.trans hw)).1
      linarith
    have hw1 : ‖w - 1‖ ≤ τ + 1 := by
      calc ‖w - 1‖ = ‖(w - s₀) + (s₀ - 1)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖w - s₀‖ + ‖s₀ - 1‖ := norm_add_le _ _
        _ ≤ 31 / 16 + (|(s₀ - 1).re| + |(s₀ - 1).im|) :=
            add_le_add hw (norm_le_abs_re_add_abs_im _)
        _ = 31 / 16 + (1 + |t|) := by simp [s₀]; norm_num
        _ ≤ τ + 1 := by simp [τ]; linarith
    have hwn : ‖w‖ ≤ τ + 2 := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ ≤ 31 / 16 + (|s₀.re| + |s₀.im|) := add_le_add hw (norm_le_abs_re_add_abs_im _)
        _ = 31 / 16 + (2 + |t|) := by simp [s₀]
        _ ≤ τ + 2 := by simp [τ]; linarith
    rcases eq_or_ne w 1 with rfl | hw1'
    · rw [DirichletCharacter.LFunctionTrivChar₁_one_apply_one, norm_one]
      nlinarith
    rw [DirichletCharacter.LFunctionTrivChar₁_one_apply_of_ne_one hw1', norm_mul]
    have hζ := TauCeti.norm_riemannZeta_le_of_re_pos (s := w) (by linarith)
    have hw10 : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw1')
    have hdiv : ‖w‖ / w.re ≤ 16 * ‖w‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg w]
    calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ ‖w - 1‖ * (‖w - 1‖⁻¹ + 1 + ‖w‖ / w.re) := by gcongr
      _ = 1 + ‖w - 1‖ * (1 + ‖w‖ / w.re) := by field_simp; ring
      _ ≤ 1 + (τ + 1) * (1 + 16 * (τ + 2)) := by
          gcongr
          exact hdiv.trans (by gcongr)
      _ ≤ 49 * τ ^ 2 := by nlinarith
  -- `49 τ² ≤ τ^9 · (1/2) ≤ τ^9 ‖L₁(s₀)‖`
  have h98 : 98 ≤ τ ^ 7 := by
    calc (98 : ℝ) ≤ 2 ^ 7 := by norm_num
      _ ≤ τ ^ 7 := pow_le_pow_left₀ (by norm_num) hτ2 7
  calc ‖DirichletCharacter.LFunctionTrivChar₁ 1 w‖ ≤ 49 * τ ^ 2 := hup
    _ = (98 * τ ^ 2) * (1 / 2) := by ring
    _ ≤ (τ ^ 7 * τ ^ 2) * ‖DirichletCharacter.LFunctionTrivChar₁ 1 s₀‖ := by
        gcongr
    _ = τ ^ 9 * ‖DirichletCharacter.LFunctionTrivChar₁ 1 s₀‖ := by ring

/-! ## Explicit zero count on discs of radius `29/16` about `2 + it` -/

/-- `log (31/29) ≥ 2/31`. -/
theorem two_div_le_log_31_29 : (2 / 31 : ℝ) ≤ Real.log (31 / 29) := by
  have := Real.one_sub_inv_le_log_of_pos (x := (31 / 29 : ℝ)) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **Explicit zero count.** The zeros of `ζ` in the closed disc of radius `29/16` about `2 + it`,
counted with analytic order, number at most `140 log(|t| + 2)`: Jensen's bound
`log M / log(R/r)` with `M = (|t| + 2)^9`, `R = 31/16`, `r = 29/16`, `1/log(31/29) ≤ 31/2`. -/
theorem count_zeros_disc_le (t : ℝ) :
    ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + t * I) (29 / 16),
      ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 140 * Real.log (|t| + 2) := by
  classical
  set c : ℂ := 2 + t * I with hcdef
  set τ : ℝ := |t| + 2 with hτ
  have hτ2 : 2 ≤ τ := by simp [τ]
  have hlogτ : 0 ≤ Real.log τ := Real.log_nonneg (by linarith)
  have hF := (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd
    isOpen_univ
  have hFc : DirichletCharacter.LFunctionTrivChar₁ 1 c ≠ 0 :=
    DirichletCharacter.LFunctionTrivChar₁_one_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re (by simp [c]))
  have hJ := (hF.mono (Set.subset_univ _)).sum_divisor_le_log_div_log (z₀ := c) (r := 29 / 16)
    (R := 31 / 16) (by norm_num) (by norm_num) hFc (M := τ ^ 9)
    fun w hw ↦ norm_LFunctionTrivChar₁_one_le_pow_mul
      (by rw [Metric.mem_sphere, dist_eq_norm] at hw; exact hw.le)
  have hdiv : ∑ᶠ ρ, MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1)
      (Metric.closedBall c (29 / 16)) ρ =
      ∑ z ∈ TauCeti.riemannZetaZerosClosedBall c (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℤ) := by
    refine (finsum_eq_sum_of_support_subset _ fun z hz ↦ ?_).trans
      (Finset.sum_congr rfl fun z hz ↦ ?_)
    · rw [Function.mem_support, TauCeti.divisor_LFunctionTrivChar₁_one_closedBall_apply] at hz
      exact TauCeti.mem_riemannZetaZerosClosedBall.mpr (by_contra fun h ↦ hz (ite_eq_right h))
    · rw [TauCeti.divisor_LFunctionTrivChar₁_one_closedBall_apply,
        ite_eq_left (TauCeti.mem_riemannZetaZerosClosedBall.mp hz)]
  rw [hdiv] at hJ
  push_cast at hJ
  rw [Real.log_pow, show ((31 / 16 : ℝ) / (29 / 16)) = 31 / 29 by norm_num] at hJ
  have hl := two_div_le_log_31_29
  have hlpos : 0 < Real.log (31 / 29 : ℝ) := by linarith
  calc _ ≤ ((9 : ℕ) : ℝ) * Real.log τ / Real.log (31 / 29) := hJ
    _ ≤ 9 * Real.log τ / (2 / 31) := by
        push_cast
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hl
    _ = 139.5 * Real.log τ := by ring
    _ ≤ 140 * Real.log τ := by gcongr; norm_num

/-! ## The window form of `ζ′/ζ` with an explicit constant -/

/-- Under the proved RH, a zero of the window `0 < Re ρ < 1`, `|Im ρ - t| ≤ 1` lies in the closed
disc of radius `29/16` about `2 + it`: `(3/2)² + 1 = 13/4 ≤ (29/16)²`. -/
theorem mem_disc_of_window {t : ℝ} {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (him : |ρ.im - t| ≤ 1) (hζ : riemannZeta ρ = 0) :
    ρ ∈ TauCeti.riemannZetaZerosClosedBall (2 + t * I) (29 / 16) := by
  refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, hζ⟩
  have hre := re_eq_half_of_zero h0 h1 hζ
  refine le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  have e1 : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have e2 : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  rw [e1, e2, hre]
  obtain ⟨hl, hu⟩ := abs_le.1 him
  nlinarith

/-- Landau's factor at `d = ‖s - s₀‖ ≤ 7/4`, radii `29/16 < 31/16`: at most `3697`. -/
theorem landau_factor_le {d : ℝ} (_hd0 : 0 ≤ d) (hd : d ≤ 7 / 4) :
    4 * (29 / 16 + d) / (29 / 16 - d) ^ 2 +
      29 / 16 / (((31 / 16 : ℝ) ^ 2 - 29 / 16 * d) * Real.log (31 / 29)) ≤ 3697 := by
  have hl := two_div_le_log_31_29
  have h1 : 4 * (29 / 16 + d) / (29 / 16 - d) ^ 2 ≤ 3648 := by
    have hp : (1 / 16 : ℝ) ≤ 29 / 16 - d := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hp hp (by norm_num) (by linarith)]
  have h2 : 29 / 16 / (((31 / 16 : ℝ) ^ 2 - 29 / 16 * d) * Real.log (31 / 29)) ≤ 49 := by
    have hp : (149 / 256 : ℝ) ≤ (31 / 16 : ℝ) ^ 2 - 29 / 16 * d := by nlinarith
    have hpos : 0 < ((31 / 16 : ℝ) ^ 2 - 29 / 16 * d) * Real.log (31 / 29) := by
      apply mul_pos <;> linarith
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul hp hl (by norm_num) (by linarith)]
  linarith

/-- **The window form of `ζ′/ζ`, explicit.** For `1/4 ≤ Re s ≤ 2`, `s ≠ 1`, `ζ(s) ≠ 0`:
`ζ′/ζ(s) + 1/(s - 1)` differs from `∑ m(ρ)/(s - ρ)` over the zeros of the window
`0 < Re ρ < 1`, `|Im ρ - Im s| ≤ 1` by at most `33413 log(|Im s| + 2)`. Landau's lemma on the
discs of radii `29/16 < 31/16` about `2 + i Im s` with `M = (|Im s| + 2)^9` gives
`3697 · 9 = 33273`; the zeros of the disc outside the window are at distance `≥ 1` from `s` and
contribute at most their count `140`. Adapted from Tau Ceti's `riemannZeta_logDeriv_window` and
`riemannZeta_local_logDeriv` (Apache 2.0). -/
theorem logDeriv_window_explicit (s : ℂ) (hs₁ : 1 / 4 ≤ s.re) (hs₂ : s.re ≤ 2) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
          ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
      33413 * Real.log (|s.im| + 2) := by
  classical
  set s₀ : ℂ := 2 + s.im * I with hs₀def
  have hs₀ : s₀.re = 2 := by simp [s₀]
  have hd : ‖s - s₀‖ ≤ 7 / 4 := by
    rw [hs₀def, norm_sub_two_add_im_mul_I, abs_le]; constructor <;> linarith
  set τ : ℝ := |s.im| + 2 with hτ
  have hτ2 : 2 ≤ τ := by simp [τ]
  have hlogτ : 0 ≤ Real.log τ := Real.log_nonneg (by linarith)
  -- Landau's lemma on the discs of radii `29/16 < 31/16`
  have hF := (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd
    isOpen_univ
  have hFb := hF.mono (Set.subset_univ (Metric.closedBall s₀ (31 / 16)))
  have hsphere : ∀ w ∈ Metric.sphere s₀ (31 / 16),
      ‖DirichletCharacter.LFunctionTrivChar₁ 1 w‖ ≤
        τ ^ 9 * ‖DirichletCharacter.LFunctionTrivChar₁ 1 s₀‖ := fun w hw ↦
    norm_LFunctionTrivChar₁_one_le_pow_mul
      (by rw [Metric.mem_sphere, dist_eq_norm] at hw; exact hw.le)
  have key := hFb.norm_logDeriv_sub_finsum_divisor_le (r := 29 / 16) (by norm_num) hsphere
    (hd.trans_lt (by norm_num)) (DirichletCharacter.LFunctionTrivChar₁_one_ne_zero hζ)
  rw [← TauCeti.logDeriv_riemannZeta_add_inv_sub_one hs1 hζ, logDeriv_apply,
    ← TauCeti.finsum_subtype_riemannZeta_eq_finsum_divisor, ← one_div,
    show ((31 / 16 : ℝ) / (29 / 16)) = 31 / 29 by norm_num, Real.log_pow] at key
  have hA := landau_factor_le (norm_nonneg (s - s₀)) hd
  -- the zeros of the disc: window and the rest
  set Z := TauCeti.riemannZetaZerosClosedBall s₀ (29 / 16) with hZ
  set W : ℂ → Prop := fun z ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1
  set f : ℂ → ℂ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)
  have hwin : ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
      f ρ = ∑ z ∈ Z with W z, f z := by
    rw [TauCeti.finsum_window_eq_sum_filter (Z := Z)
      (fun z h0 h1 him hz ↦ mem_disc_of_window h0 h1 him hz) f]
    refine Finset.sum_congr (Finset.filter_congr fun z hz ↦ ?_) fun _ _ ↦ rfl
    exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1⟩,
      fun h ↦ ⟨h.1, h.2.1, h.2.2, (TauCeti.mem_riemannZetaZerosClosedBall.mp hz).2⟩⟩
  have hrest : ‖∑ z ∈ Z with ¬W z, f z‖ ≤ 140 * Real.log τ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z hz ↦ ?_).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ ↦ by positivity).trans (count_zeros_disc_le s.im)))
    obtain ⟨hzZ, hzW⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzd, hzζ⟩ := TauCeti.mem_riemannZetaZerosClosedBall.mp hzZ
    show ‖((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)‖ ≤
      ((analyticOrderAt riemannZeta z).toNat : ℝ)
    rw [norm_div, Complex.norm_natCast]
    refine div_le_self (by positivity) ?_
    have hzre : 0 < z.re := by
      have := abs_re_le_norm (z - s₀)
      rw [sub_re, hs₀] at this
      linarith [(abs_le.1 (this.trans hzd)).1]
    have hz1 : z.re < 1 := TauCeti.re_lt_one_of_riemannZeta_eq_zero hzζ
    have hgt : 1 < |z.im - s.im| := by
      by_contra h
      exact hzW ⟨hzre, hz1, not_lt.mp h⟩
    rw [abs_sub_comm] at hgt
    exact hgt.le.trans (by simpa using abs_im_le_norm (s - z))
  have hsplit := Finset.sum_filter_add_sum_filter_not Z W f
  rw [finsum_subtype_riemannZeta_eq_sum' s₀ (29 / 16) f, ← hsplit] at key
  rw [hwin]
  calc _ = ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ((∑ z ∈ Z with W z, f z) + ∑ z ∈ Z with ¬W z, f z)) + ∑ z ∈ Z with ¬W z, f z‖ := by
        rw [sub_add_eq_sub_sub, sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ (4 * (29 / 16 + ‖s - s₀‖) / (29 / 16 - ‖s - s₀‖) ^ 2 +
          29 / 16 / (((31 / 16 : ℝ) ^ 2 - 29 / 16 * ‖s - s₀‖) * Real.log (31 / 29))) *
          (((9 : ℕ) : ℝ) * Real.log τ) + 140 * Real.log τ := add_le_add key hrest
    _ ≤ 33413 * Real.log τ := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hA hlogτ]

/-- **`ζ′/ζ + 1/(s - 1)` at horizontal distance `a` from the critical line, explicit**: for
`0 < a ≤ 1`, `s ≠ 1`, `1/4 ≤ Re s ≤ 2`, `a ≤ |Re s - 1/2|`,
`‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ 33553 / a · log(|Im s| + 2)` (`33553 = 33413 + 140`). Same proof as
`WallsMeetRHVonKoch.logDeriv_bound_of_RH_dist` with the explicit window form and zero count. -/
theorem logDeriv_bound_explicit : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, s ≠ 1 →
    1 / 4 ≤ s.re → s.re ≤ 2 → a ≤ |s.re - 1 / 2| →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 33553 / a * Real.log (|s.im| + 2) := by
  classical
  intro a ha ha1 s hs1 hs hs2 hd
  set t := s.im with ht
  set L := Real.log (|t| + 2)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg t])
  have hζ : riemannZeta s ≠ 0 := by
    rcases lt_or_gt_of_ne (show s.re ≠ 1 / 2 by
      intro h; rw [h, sub_self, abs_zero] at hd; linarith) with h | h
    · intro h0
      have := re_eq_half_of_zero (by linarith) (by linarith) h0
      linarith
    · exact riemannZeta_ne_zero_of_half_lt h
  have hw := logDeriv_window_explicit s hs hs2 hs1 hζ
  set m : ℂ → ℕ := fun z ↦ (analyticOrderAt riemannZeta z).toNat
  set Z := TauCeti.riemannZetaZerosClosedBall (2 + t * I) (29 / 16)
  rw [← ht, TauCeti.finsum_window_eq_sum_filter (Z := Z)
    (fun z h0 h1 him hz ↦ mem_disc_of_window h0 h1 him hz)
    fun z ↦ (m z : ℂ) / (s - z)] at hw
  set W := ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0,
    (m z : ℂ) / (s - z)
  have hcount : ∑ z ∈ Z, (m z : ℝ) ≤ 140 * L := count_zeros_disc_le t
  have hW : ‖W‖ ≤ 140 * L / a := by
    calc ‖W‖ ≤ ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0,
          (m z : ℝ) / a := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz ↦ ?_)
          obtain ⟨-, h0, h1, -, hzζ⟩ := Finset.mem_filter.mp hz
          rw [norm_div, Complex.norm_natCast]
          refine div_le_div_of_nonneg_left (by positivity) ha ?_
          have hre : a ≤ |(s - z).re| := by rw [sub_re, re_eq_half_of_zero h0 h1 hzζ]; exact hd
          exact hre.trans (abs_re_le_norm _)
      _ ≤ ∑ z ∈ Z, (m z : ℝ) / a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ ↦ by positivity
      _ = (∑ z ∈ Z, (m z : ℝ)) / a := by rw [Finset.sum_div]
      _ ≤ 140 * L / a := by gcongr
  set H := deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
  have htri : ‖H‖ ≤ ‖H - W‖ + ‖W‖ := by
    have := norm_add_le (H - W) W
    rwa [sub_add_cancel] at this
  have h1 : 33413 * L ≤ 33413 * L / a := le_div_self (by positivity) ha ha1
  calc ‖H‖ ≤ 33413 * L + 140 * L / a := by linarith
    _ ≤ 33413 * L / a + 140 * L / a := add_le_add h1 le_rfl
    _ = 33553 / a * L := by ring

/-! ## The explicit `C¹` bump and its Mellin bound (`168`) -/

section
open Set MeasureTheory Complex Filter Asymptotics
open scoped Topology Interval

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

end

/-! ## `∑ m(ρ)/|ρ|` from the explicit disc count -/

section


/-- From the proved `riemannHypothesis` (copied from the von Koch file): a zero of `ζ` in the
strip `0 < Re ρ < 1` has `Re ρ = 1/2`. -/
theorem zsum_re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

theorem zsum_one_le_log_add_two {T : ℝ} (hT : 1 ≤ T) : 1 ≤ Real.log (T + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- The half-plane case, `σ = ±1`. -/
theorem zsum_half {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 1 ≤ T) (P : Finset ℂ)
    (hP : ∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ 0 ≤ σ * z.im ∧ σ * z.im ≤ T) :
    ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤
      8 * Cc * Real.log (T + 2) * (1 + Real.log (T + 1)) := by
  classical
  set m : ℂ → ℝ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set N := ⌊T⌋₊
  have hmaps : ∀ z ∈ P, ⌊σ * z.im⌋₊ ∈ Finset.range (N + 1) := fun z hz ↦ by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hP z hz).2.2.2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlogT : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hfib : ∀ k ∈ Finset.range (N + 1),
      ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖ ≤
        8 * Cc * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ := fun k hk ↦ by
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    -- the fibre lies in the disc of radius `29/16` about `2 + iσ(k + 1/2)`
    have hsub : P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k) ⊆
        TauCeti.riemannZetaZerosClosedBall (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I) (29 / 16) := by
      intro z hz
      obtain ⟨hzP, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3, h4⟩ := hP z hzP
      have hre : z.re = 1 / 2 := zsum_re_eq_half_of_zero (by linarith)
        (TauCeti.re_lt_one_of_riemannZeta_eq_zero hζ) hζ
      have hfl := Nat.floor_le h3
      have hfl' := Nat.lt_floor_add_one (σ * z.im)
      rw [hzk] at hfl hfl'
      refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, hζ⟩
      set w := z - (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I)
      have hwre : w.re = z.re - 2 := by simp [w]
      have hwim : w.im = σ * (σ * z.im - (k + 1 / 2)) := by
        simp only [w, sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
        norm_num
        linear_combination (-z.im) * hσσ
      have hsq : ‖w‖ ^ 2 ≤ (29 / 16) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim, hre]
        have : (σ * (σ * z.im - (k + 1 / 2))) * (σ * (σ * z.im - (k + 1 / 2))) =
            (σ * z.im - (k + 1 / 2)) ^ 2 := by
          linear_combination (σ * z.im - (k + 1 / 2)) ^ 2 * hσσ
        rw [this]
        nlinarith
      nlinarith [norm_nonneg w]
    have hnorm : ∀ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), 1 / ‖z‖ ≤ 4 * ((k : ℝ) + 1)⁻¹ :=
      fun z hz ↦ by
      obtain ⟨hzP, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3, h4⟩ := hP z hzP
      have hfl := Nat.floor_le h3
      rw [hzk] at hfl
      have hre : 1 / 4 ≤ ‖z‖ := h1.trans ((le_abs_self _).trans (abs_re_le_norm z))
      have him : (k : ℝ) ≤ ‖z‖ := by
        calc (k : ℝ) ≤ σ * z.im := hfl
          _ ≤ |σ * z.im| := le_abs_self _
          _ = |z.im| := by rw [abs_mul, hσabs, one_mul]
          _ ≤ ‖z‖ := abs_im_le_norm z
      have hz0 : 0 < ‖z‖ := by linarith
      rw [div_le_iff₀ hz0]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num; linarith
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        rw [show 4 * ((k : ℝ) + 1)⁻¹ * ‖z‖ = 4 * ‖z‖ / (k + 1) by ring, le_div_iff₀ (by linarith)]
        nlinarith
    have hcount : ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z ≤
        2 * Cc * Real.log (T + 2) := by
      have h := hCc (σ * (k + 1 / 2))
      rw [abs_mul, hσabs, one_mul, abs_of_nonneg (by positivity)] at h
      have hk' : (k : ℝ) ≤ T := by
        have : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact this.trans (Nat.floor_le (by linarith))
      have hlog : Real.log ((k : ℝ) + 1 / 2 + 2) ≤ 2 * Real.log (T + 2) := by
        rw [show (2 : ℝ) * Real.log (T + 2) = ((2 : ℕ) : ℝ) * Real.log (T + 2) by norm_num,
          ← Real.log_pow]
        exact Real.log_le_log (by positivity) (by nlinarith)
      calc ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z
          ≤ ∑ z ∈ TauCeti.riemannZetaZerosClosedBall
              (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I) (29 / 16), m z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
        _ ≤ Cc * Real.log ((k : ℝ) + 1 / 2 + 2) := h
        _ ≤ Cc * (2 * Real.log (T + 2)) := by gcongr
        _ = 2 * Cc * Real.log (T + 2) := by ring
    calc ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖
        ≤ ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z * (4 * ((k : ℝ) + 1)⁻¹) := by
          refine Finset.sum_le_sum fun z hz ↦ ?_
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (hnorm z hz) (by positivity)
      _ = (∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z) * (4 * ((k : ℝ) + 1)⁻¹) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * Cc * Real.log (T + 2) * (4 * ((k : ℝ) + 1)⁻¹) := by gcongr
      _ = _ := by ring
  have hharm : ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ ≤ 1 + Real.log (T + 1) := by
    have h := harmonic_le_one_add_log (N + 1)
    have hcast : ((harmonic (N + 1) : ℚ) : ℝ) = ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
      simp only [harmonic]
      push_cast
      rfl
    rw [hcast] at h
    refine h.trans ?_
    have : ((N + 1 : ℕ) : ℝ) ≤ T + 1 := by
      push_cast; linarith [Nat.floor_le (show (0 : ℝ) ≤ T by linarith)]
    linarith [Real.log_le_log (by positivity) this]
  calc ∑ k ∈ Finset.range (N + 1), ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖
      ≤ ∑ k ∈ Finset.range (N + 1), 8 * Cc * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ :=
        Finset.sum_le_sum hfib
    _ = 8 * Cc * Real.log (T + 2) * ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 8 * Cc * Real.log (T + 2) * (1 + Real.log (T + 1)) := by gcongr

/-- **`∑ m(ρ)/|ρ| ≤ 32 Cc log²(T + 2)`** over any finite set of zeros of `ζ` with
`1/4 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`, `T ≥ 1`, given the count `Cc log(|t| + 2)` on the discs of
radius `29/16` about `2 + i t`. -/
theorem sum_order_div_norm_le_of {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2)) :
    ∀ T : ℝ, 1 ≤ T → ∀ P : Finset ℂ,
      (∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ |z.im| ≤ T) →
      ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤
        32 * Cc * Real.log (T + 2) ^ 2 := by
  classical
  intro T hT P hP
  have hup := zsum_half hCc0 hCc (Or.inl rfl) hT (P.filter fun z ↦ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by simpa using h0, by rw [one_mul]; exact (le_abs_self _).trans h3⟩
  have hdn := zsum_half hCc0 hCc (Or.inr rfl) hT (P.filter fun z ↦ ¬ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by rw [neg_one_mul]; linarith [not_le.mp h0], by
        rw [neg_one_mul]; exact (neg_le_abs _).trans h3⟩
  rw [← Finset.sum_filter_add_sum_filter_not P fun z ↦ 0 ≤ z.im]
  have hl1 : 1 ≤ Real.log (T + 2) := zsum_one_le_log_add_two hT
  have hl2 : Real.log (T + 1) ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
  nlinarith [mul_nonneg hCc0 (sub_nonneg.2 hl1), mul_nonneg hCc0 (sub_nonneg.2 hl2),
    mul_nonneg (mul_nonneg hCc0 (sub_nonneg.2 hl1)) (sub_nonneg.2 hl2)]

end

/-! ## The safe height from the explicit window form and disc count -/

section


/-- From the proved `riemannHypothesis`: a zero of `ζ` in the strip `0 < Re ρ < 1` has
`Re ρ = 1/2`. -/
theorem safe_re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): a zero outside the window about `s` is at
distance at least `1` from `s`, when `1/4 ≤ Re s`. -/
theorem safe_one_le_norm_sub_of_riemannZeta_eq_zero {s ρ : ℂ} (hs : 1 / 4 ≤ s.re)
    (hρ : riemannZeta ρ = 0) (hw : ¬(0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - s.im| ≤ 1)) :
    1 ≤ ‖s - ρ‖ := by
  rcases le_or_gt ρ.re 0 with h0 | h0
  · obtain ⟨n, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h0).mp hρ
    have hre : (s - -2 * ((n : ℂ) + 1)).re = s.re + 2 * (n + 1) := by simp
    refine le_trans ?_ ((le_abs_self _).trans (abs_re_le_norm _))
    rw [hre]
    linarith [n.cast_nonneg (α := ℝ)]
  rcases lt_or_ge ρ.re 1 with h1 | h1
  · have : 1 < |ρ.im - s.im| := by
      by_contra h
      exact hw ⟨h0, h1, not_lt.mp h⟩
    rw [abs_sub_comm] at this
    exact this.le.trans (by simpa using abs_im_le_norm (s - ρ))
  · exact absurd hρ (riemannZeta_ne_zero_of_one_le_re h1)

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): the window sum over a finite set `Z`
containing the window zeros, all at distance `≥ δ > 0` from `s`, is at most `∑_Z m / δ`. -/
theorem safe_norm_finsum_window_le {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    ‖∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
      (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ := by
  classical
  rw [TauCeti.finsum_window_eq_sum_filter hZ
    fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z), Finset.sum_div]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z hz ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity))
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (by positivity) hδ (hsep z (Finset.mem_filter.mp hz).1)

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): the estimate at a separated point. -/
theorem safe_riemannZeta_ne_zero_and_norm_logDeriv_le {C : ℝ}
    (hC : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s.im| + 2))
    {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ) (hs₁ : 1 / 4 ≤ s.re) (hs₂ : s.re ≤ 2)
    (hsim : 2 ≤ |s.im|)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    riemannZeta s ≠ 0 ∧ ‖deriv riemannZeta s / riemannZeta s‖ ≤
      C * Real.log (|s.im| + 2) + (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ + 1 := by
  have hζ : riemannZeta s ≠ 0 := fun hζ ↦ by
    by_cases hw : 0 < s.re ∧ s.re < 1 ∧ |s.im - s.im| ≤ 1
    · have := hsep s (hZ s hw.1 hw.2.1 hw.2.2 hζ)
      rw [sub_self, norm_zero] at this
      linarith
    · have := safe_one_le_norm_sub_of_riemannZeta_eq_zero hs₁ hζ hw
      rw [sub_self, norm_zero] at this
      linarith
  refine ⟨hζ, ?_⟩
  have hs1 : 2 ≤ ‖s - 1‖ := hsim.trans (by simpa using abs_im_le_norm (s - 1))
  have hpole : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hs1' : s ≠ 1 := fun h ↦ by norm_num [h] at hs1
  set W := ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
    ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)
  have hsplit : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - W) + W - 1 / (s - 1) := by ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (hC s hs₁ hs₂ hs1' hζ) (safe_norm_finsum_window_le hδ hZ hsep))) hpole)

/-- A zero `ρ` with `Re ρ = 1/2` and `|Im ρ - t| ≤ 1/2` lies in the closed disc of radius
`29/16` about `2 + i t` (distance `≤ √10 / 2 < 29/16`). -/
theorem safe_mem_ball {ρ : ℂ} {t : ℝ} (hre : ρ.re = 1 / 2) (him : |ρ.im - t| ≤ 1 / 2)
    (hζ : riemannZeta ρ = 0) :
    ρ ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16) := by
  refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, hζ⟩
  have h1 : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have h2 : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ 10 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2, hre]
    have := abs_le.mp him
    nlinarith
  nlinarith [norm_nonneg (ρ - (2 + t * I))]

/-- The disc of radius `29/16` about `2 + i t`. -/
noncomputable abbrev safe_B (t : ℝ) : Finset ℂ :=
  TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16)

/-- The six discs covering the window zeros at heights `±T′`, `T′ ∈ [T, T + 1]`. -/
noncomputable abbrev safe_Z (T : ℝ) : Finset ℂ :=
  safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2)) ∪ safe_B (-(T + 1 / 2)) ∪ safe_B (-(T + 3 / 2))

/-- Every window zero about `s` with `T ≤ |Im s| ≤ T + 1` lies in `safe_Z T`. -/
theorem safe_mem_Z {T : ℝ} {s ρ : ℂ} (hT : T ≤ |s.im|) (hT' : |s.im| ≤ T + 1)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hw : |ρ.im - s.im| ≤ 1) (hζ : riemannZeta ρ = 0) :
    ρ ∈ safe_Z T := by
  have hre := safe_re_eq_half_of_zero h0 h1 hζ
  have him : |(|ρ.im| - T)| ≤ 2 ∧ |(|ρ.im| - (T + 1))| ≤ 2 := by
    have := (abs_abs_sub_abs_le_abs_sub ρ.im s.im).trans hw
    rw [abs_le] at this
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have ha := abs_le.mp him.1
  have hb := abs_le.mp him.2
  simp only [safe_Z, Finset.mem_union]
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at ha hb
    rcases le_or_gt ρ.im T with h2 | h2
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    rcases le_or_gt ρ.im (T + 1) with h3 | h3
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
  · rw [abs_of_neg h] at ha hb
    rcases le_or_gt (-ρ.im) T with h2 | h2
    · exact Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    rcases le_or_gt (-ρ.im) (T + 1) with h3 | h3
    · exact Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    · exact Or.inr <| safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ

/-- A sum of the nonnegative weights `m` over a union is at most the sum of the two sums. -/
theorem safe_sum_union_le (A B : Finset ℂ) :
    ∑ z ∈ A ∪ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ (∑ z ∈ A, ((analyticOrderAt riemannZeta z).toNat : ℝ)) + ∑ z ∈ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  classical
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B)
    (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ))
  have h0 : 0 ≤ ∑ z ∈ A ∩ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by positivity
  linarith

/-- The zeros of `safe_Z T`, counted with order, number at most `12 |Cc| log (T + 2)`. -/
theorem safe_sum_Z_le {Cc : ℝ}
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2))
    {T : ℝ} (hT : 2 ≤ T) :
    ∑ z ∈ safe_Z T, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 12 * |Cc| * Real.log (T + 2) := by
  have hdisc (t : ℝ) (ht : |t| ≤ T + 3 / 2) :
      ∑ z ∈ safe_B t, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 2 * |Cc| * Real.log (T + 2) := by
    have hlog : Real.log (|t| + 2) ≤ 2 * Real.log (T + 2) :=
      Real.log_add_two_le_two_mul_log_add_two (by linarith) (abs_nonneg _)
        (by linarith)
    have hl0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    calc ∑ z ∈ safe_B t, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2) := hCc t
      _ ≤ |Cc| * Real.log (|t| + 2) := mul_le_mul_of_nonneg_right (le_abs_self Cc) hl0
      _ ≤ |Cc| * (2 * Real.log (T + 2)) := mul_le_mul_of_nonneg_left hlog (abs_nonneg Cc)
      _ = _ := by ring
  have a1 := hdisc (T - 1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a2 := hdisc (T + 1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a3 := hdisc (T + 3 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a4 := hdisc (-(T - 1 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have a5 := hdisc (-(T + 1 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have a6 := hdisc (-(T + 3 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have u5 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2)) ∪ safe_B (-(T + 1 / 2))) (safe_B (-(T + 3 / 2)))
  have u4 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2))) (safe_B (-(T + 1 / 2)))
  have u3 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2))
    (safe_B (-(T - 1 / 2)))
  have u2 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2)) (safe_B (T + 3 / 2))
  have u1 := safe_sum_union_le (safe_B (T - 1 / 2)) (safe_B (T + 1 / 2))
  simp only [safe_Z]
  linarith

/-- Every point of a finite set of zeros has order `≥ 1`: adapted from Tau Ceti Window.lean
(Apache 2.0). -/
theorem safe_card_image_abs_im_le_sum {Z : Finset ℂ} (hZ : ∀ z ∈ Z, riemannZeta z = 0) :
    ((Z.image fun z ↦ |z.im|).card : ℝ) ≤ ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun z hz ↦ by
    exact_mod_cast TauCeti.one_le_toNat_analyticOrderAt_riemannZeta (hZ z hz)

/-- The final arithmetic, adapted from Tau Ceti Window.lean (Apache 2.0): if `1 ≤ L`,
`0 ≤ l ≤ 2 L` and `0 ≤ K ≤ 12 |C'| L`, then
`C l + 2 K (K + 1) + 1 ≤ (2 |C| + 288 C'² + 24 |C'| + 1) L²`. -/
theorem safe_final_arith {C C' K L l : ℝ} (hL : 1 ≤ L) (hl : 0 ≤ l)
    (hlL : l ≤ 2 * L) (hK0 : 0 ≤ K) (hK : K ≤ 12 * |C'| * L) :
    C * l + 2 * K * (K + 1) + 1 ≤ (2 * |C| + 288 * C' ^ 2 + 24 * |C'| + 1) * L ^ 2 := by
  have hC : C * l ≤ |C| * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hl).trans
      (mul_le_mul_of_nonneg_left hlL (abs_nonneg C))
  have hL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith [abs_nonneg C', abs_nonneg C, sq_abs C',
    mul_le_mul hK hK hK0 (by nlinarith [abs_nonneg C']),
    mul_le_mul_of_nonneg_left hL2 (abs_nonneg C), mul_le_mul_of_nonneg_left hL2 (abs_nonneg C')]

open Complex in
/-- **An explicit safe height for `ζ′/ζ`**, adapted from Tau Ceti Window.lean
(`riemannZeta_safe_height`, Apache 2.0, The Tau Ceti contributors). -/
theorem riemannZeta_safe_height_of {Cw Cc : ℝ}
    (hCw : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        Cw * Real.log (|s.im| + 2))
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2)) :
    ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1), ∀ σ : ℝ, 1 / 4 ≤ σ → σ ≤ 2 →
      ∀ s ∈ ({(σ : ℂ) + (T' : ℂ) * I, (σ : ℂ) - (T' : ℂ) * I} : Set ℂ),
        riemannZeta s ≠ 0 ∧
          ‖deriv riemannZeta s / riemannZeta s‖ ≤
            (2 * |Cw| + 288 * Cc ^ 2 + 24 * |Cc| + 1) * Real.log (T + 2) ^ 2 := by
  classical
  intro T hT
  set Z := safe_Z T
  set K := ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hcard := safe_card_image_abs_im_le_sum (Z := Z) fun z hz ↦ by
    simp only [Z, safe_Z, Finset.mem_union] at hz
    rcases hz with ((((hz | hz) | hz) | hz) | hz) | hz <;>
      exact (TauCeti.mem_riemannZetaZerosClosedBall.1 hz).2
  obtain ⟨T', hT', hsepT'⟩ := TauCeti.exists_mem_Icc_forall_le_abs_sub
    (Z.image fun z ↦ |z.im|) (by linarith : T ≤ T + 1)
  have hδ : 1 / (2 * (K + 1)) ≤ (T + 1 - T) / (2 * ((Z.image fun z ↦ |z.im|).card + 1)) := by
    rw [add_sub_cancel_left]
    gcongr
  refine ⟨T', hT', fun σ hσ₁ hσ₂ s hs ↦ ?_⟩
  have hsre : s.re = σ := by rcases hs with rfl | rfl <;> simp
  have hsim : |s.im| = T' := by
    rcases hs with rfl | rfl <;> simp [abs_of_nonneg (by linarith [hT'.1] : (0 : ℝ) ≤ T')]
  have hsep (z : ℂ) (hz : z ∈ Z) : 1 / (2 * (K + 1)) ≤ ‖s - z‖ := by
    refine (hδ.trans (hsepT' _ (Finset.mem_image_of_mem _ hz))).trans ?_
    rw [← hsim]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by simpa using abs_im_le_norm (s - z))
  obtain ⟨hζ, hbound⟩ := safe_riemannZeta_ne_zero_and_norm_logDeriv_le hCw (Z := Z)
    (one_div_pos.2 (by linarith)) (hsre ▸ hσ₁) (hsre ▸ hσ₂) (by linarith [hT'.1])
    (fun z h1 h2 h3 h4 ↦ safe_mem_Z (hsim ▸ hT'.1) (hsim ▸ hT'.2) h1 h2 h3 h4) hsep
  refine ⟨hζ, hbound.trans ?_⟩
  have hlog : Real.log (|s.im| + 2) ≤ 2 * Real.log (T + 2) :=
    Real.log_add_two_le_two_mul_log_add_two (by linarith) (abs_nonneg _)
      (by linarith [hT'.2])
  have hKδ : K / (1 / (2 * (K + 1))) = 2 * K * (K + 1) := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [hKδ]
  exact safe_final_arith
    ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9]))
    (Real.log_nonneg (by linarith [abs_nonneg s.im])) hlog hK0 (safe_sum_Z_le hCc hT)

end

open scoped Real in
/-- The arithmetic of the explicit-formula terms at `T ≥ x = s²`, `ε = 1/s`, `L = log x ≥ 4`:
tails, left edge (`q = x^(1/4) ≤ s`, `A = log(T + 2) ≤ 2L`, `B = log(1 + 4T) ≤ 2L`), two horizontal
edges (`Q = log(x + 2) ≤ 2L`, `y = x^{σ₀} ≤ e x`), residues, smoothing, main-term correction. -/
private lemma vk_terms_le {C C₁ Cs Cz x s L T A B Q q y e σ₀ : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hCs : 0 ≤ Cs) (hCz : 0 ≤ Cz) (hs : 1 ≤ s) (hx : x = s ^ 2) (hL : 4 ≤ L) (hT : x ≤ T)
    (hA : 0 ≤ A) (hA2 : A ≤ 2 * L) (hB : 0 ≤ B) (hB2 : B ≤ 2 * L) (hQ : 0 ≤ Q) (hQ2 : Q ≤ 2 * L)
    (hq : 0 ≤ q) (hqs : q ≤ s) (he : 0 < e) (hy : 0 ≤ y) (hye : y ≤ e * x)
    (hσ₀ : 0 ≤ σ₀ - 1 / 4) (hσ₀' : σ₀ - 1 / 4 ≤ 1) :
    1 / (2 * π) * (2 * (8 * L ^ 2 * C * (e * x)) / (s⁻¹ * T) +
        4 * ((4 * C₁ * A + 4 / 3) * C * q) * B +
        ((σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2) +
          (σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2))) +
      C * s * (Cz * A ^ 2) + 3 * (2 * s⁻¹ * x + 1) * L + 2 * Real.log 2 * s⁻¹ * x ≤
    (16 * e * C + (64 * C₁ + 11) * C + 8 * e * Cs * C + 4 * C * Cz + 11) * s * L ^ 2 := by
  subst hx
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hL2 : 16 ≤ L ^ 2 := by nlinarith
  have hπ : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hπ0 : 0 ≤ 1 / (2 * π) := by positivity
  have hT0 : 0 < T := by nlinarith
  have hsT : s ≤ s⁻¹ * T := by rw [inv_mul_eq_div, le_div_iff₀ hs0]; nlinarith
  have hsT2 : s ^ 3 ≤ s⁻¹ * T ^ 2 := by
    rw [inv_mul_eq_div, le_div_iff₀ hs0]
    have := pow_le_pow_left₀ (by positivity) hT 2
    nlinarith
  have hW0 : 0 ≤ s * L ^ 2 := by positivity
  have hW1 : L ^ 2 ≤ s * L ^ 2 := le_mul_of_one_le_left (by positivity) hs
  have t1 : 2 * (8 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * T) ≤ 16 * e * C * (s * L ^ 2) := by
    calc _ ≤ 2 * (8 * L ^ 2 * C * (e * s ^ 2)) / s :=
          div_le_div_of_nonneg_left (by positivity) hs0 hsT
      _ = 16 * e * C * (s * L ^ 2) := by field_simp; ring
  have t2 : 4 * ((4 * C₁ * A + 4 / 3) * C * q) * B ≤ (64 * C₁ + 11) * C * (s * L ^ 2) := by
    calc 4 * ((4 * C₁ * A + 4 / 3) * C * q) * B
        ≤ 4 * ((4 * C₁ * (2 * L) + 4 / 3) * C * s) * (2 * L) := by gcongr
      _ ≤ (64 * C₁ + 11) * C * (s * L ^ 2) := by
          have hLL : L ≤ L ^ 2 := by nlinarith
          nlinarith [mul_nonneg (mul_nonneg hC hs0.le) (sub_nonneg.2 hLL)]
  have hQ2' : Q ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have t3 : (σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2) ≤ 4 * e * Cs * C * (s * L ^ 2) := by
    calc (σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2)
        ≤ 1 * (Cs * (4 * L ^ 2) * C) * (e * s ^ 2) / s ^ 3 := by gcongr
      _ = 4 * e * Cs * C * L ^ 2 / s := by field_simp
      _ ≤ 4 * e * Cs * C * L ^ 2 := div_le_self (by positivity) hs
      _ ≤ 4 * e * Cs * C * (s * L ^ 2) := by gcongr
  have t4 : C * s * (Cz * A ^ 2) ≤ 4 * C * Cz * (s * L ^ 2) := by
    have : A ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    calc C * s * (Cz * A ^ 2) ≤ C * s * (Cz * (4 * L ^ 2)) := by gcongr
      _ = 4 * C * Cz * (s * L ^ 2) := by ring
  have t5 : 3 * (2 * s⁻¹ * s ^ 2 + 1) * L ≤ 9 * (s * L ^ 2) := by
    rw [show 2 * s⁻¹ * s ^ 2 = 2 * s by field_simp]
    nlinarith
  have t6 : 2 * Real.log 2 * s⁻¹ * s ^ 2 ≤ 2 * (s * L ^ 2) := by
    rw [show 2 * Real.log 2 * s⁻¹ * s ^ 2 = 2 * Real.log 2 * s by field_simp]
    have := Real.log_two_lt_d9
    have := Real.log_pos one_lt_two
    nlinarith
  have h3' : 0 ≤ (σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg hσ₀ (by positivity)) hy) (by positivity)
  have hsum0 : 0 ≤ 2 * (8 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * T) +
      4 * ((4 * C₁ * A + 4 / 3) * C * q) * B +
      ((σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2) +
        (σ₀ - 1 / 4) * (Cs * Q ^ 2 * C) * y / (s⁻¹ * T ^ 2)) :=
    add_nonneg (add_nonneg (div_nonneg (by positivity) (mul_nonneg (by positivity) hT0.le))
      (by positivity)) (add_nonneg h3' h3')
  have hmul := mul_le_of_le_one_left hsum0 hπ
  have hD : (16 * e * C + (64 * C₁ + 11) * C + 8 * e * Cs * C + 4 * C * Cz + 11) * s * L ^ 2 =
      16 * e * C * (s * L ^ 2) + (64 * C₁ + 11) * C * (s * L ^ 2) +
        (4 * e * Cs * C * (s * L ^ 2) + 4 * e * Cs * C * (s * L ^ 2)) +
        4 * C * Cz * (s * L ^ 2) + 9 * (s * L ^ 2) + 2 * (s * L ^ 2) := by ring
  rw [hD]
  linarith


/-! ## Von Koch's bound with every constant a numeral -/

set_option maxHeartbeats 800000 in
open scoped Chebyshev in
/-- The von Koch proof of `WallsMeetRHVonKoch.psi_sub_le_sqrt_log_sq` with its four existential
inputs replaced by `logDeriv_bound_explicit` (`C₁ = 33553`), `riemannZeta_safe_height_of` at
`Cw = 33413`, `Cc = 140` (`Cs = 2·33413 + 288·140² + 24·140 + 1 = 5714987`),
`sum_order_div_norm_le_of` at `Cc = 140` (`Cz = 4480`) and `exists_explicit_bump` (`C = 168`).
The constants are kept as names with defining equations so that the body is the von Koch body. -/
theorem psi_sub_le_explicit_aux : ∃ C C₁ Cs Cz : ℝ, C = 168 ∧ C₁ = 33553 ∧
    Cs = 2 * |(33413 : ℝ)| + 288 * (140 : ℝ) ^ 2 + 24 * |(140 : ℝ)| + 1 ∧ Cz = 32 * 140 ∧
    ∀ x : ℝ, 55 ≤ x → |ψ x - x| ≤
      (16 * Real.exp 1 * C + (64 * C₁ + 11) * C + 8 * Real.exp 1 * |Cs| * C + 4 * C * Cz + 11) *
        √x * Real.log x ^ 2 := by
  classical
  obtain ⟨C₁, hC₁def, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 33553 ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, s ≠ 1 →
      1 / 4 ≤ s.re → s.re ≤ 2 → a ≤ |s.re - 1 / 2| →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ / a * Real.log (|s.im| + 2) :=
    ⟨33553, rfl, logDeriv_bound_explicit⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; norm_num
  obtain ⟨Cs, hCsdef, hCs⟩ : ∃ Cs : ℝ,
      Cs = 2 * |(33413 : ℝ)| + 288 * (140 : ℝ) ^ 2 + 24 * |(140 : ℝ)| + 1 ∧
      ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1), ∀ σ : ℝ, 1 / 4 ≤ σ → σ ≤ 2 →
        ∀ s ∈ ({(σ : ℂ) + (T' : ℂ) * I, (σ : ℂ) - (T' : ℂ) * I} : Set ℂ),
          riemannZeta s ≠ 0 ∧
            ‖deriv riemannZeta s / riemannZeta s‖ ≤ Cs * Real.log (T + 2) ^ 2 :=
    ⟨_, rfl, riemannZeta_safe_height_of (Cw := 33413) (Cc := 140) logDeriv_window_explicit
      count_zeros_disc_le⟩
  obtain ⟨Cz, hCzdef, hCz⟩ : ∃ Cz : ℝ, Cz = 32 * 140 ∧ ∀ T : ℝ, 1 ≤ T → ∀ P : Finset ℂ,
      (∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ |z.im| ≤ T) →
      ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤ Cz * Real.log (T + 2) ^ 2 :=
    ⟨_, rfl, sum_order_div_norm_le_of (Cc := 140) (by norm_num) count_zeros_disc_le⟩
  have hCz0 : 0 ≤ Cz := by rw [hCzdef]; norm_num
  obtain ⟨ν, hν1, hν0', hνs', hνm, hCb⟩ := exists_explicit_bump
  have hνi := TauCeti.integrableOn_div_of_continuousOn_of_support_subset
    (hν1.continuousOn.mono TauCeti.Icc_one_half_two_subset_Ioi) hνs'
  obtain ⟨C, hCdef, hC⟩ : ∃ C : ℝ, C = 168 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 4 ≤ s.re →
      s.re ≤ 2 → ‖mellin (fun x ↦ (TauCeti.smoothCutoff ν ε x : ℂ)) s‖ ≤
        C / (‖s‖ * (1 + ε * ‖s‖)) :=
    ⟨168, rfl, hCb⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; norm_num
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  -- the regular part `G = -ζ′/ζ - 1/(s - 1)` of the L-series of `Λ`
  set G : ℂ → ℂ := fun s ↦ -logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s with hGdef
  have hGd : ∀ s : ℂ, riemannZeta s ≠ 0 → DifferentiableAt ℂ G s := fun s hs ↦ by
    have hd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    exact (((hd.analyticAt s).deriv).differentiableAt.div (hd s)
      (DirichletCharacter.LFunctionTrivChar₁_one_ne_zero hs)).neg
  have hGmer : ∀ s : ℂ, MeromorphicAt G s := fun s ↦
    (((DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt
      s).meromorphicAt.logDeriv).neg
  have hGeq : ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
      G s = -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) := fun s hs1 hs ↦ by
    simp only [G]
    rw [one_div, ← logDeriv_apply, TauCeti.logDeriv_riemannZeta_add_inv_sub_one hs1 hs]
  have hGU : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} := fun s hs ↦
    (hGd s (riemannZeta_ne_zero_of_half_lt hs)).differentiableWithinAt
  have hG1 : AnalyticAt ℂ G 1 := hGU.analyticAt (hU.mem_nhds (by simp; norm_num))
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      1 * Real.log (n + 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have hLG (s : ℂ) (hs : 1 < s.re) :
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s = G s + 1 / (s - 1) := by
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      hGeq s hs1 (riemannZeta_ne_zero_of_half_lt (by linarith))]
    ring
  have hCs0 : 0 ≤ |Cs| := abs_nonneg _
  refine ⟨C, C₁, Cs, Cz, hCdef, hC₁def, hCsdef, hCzdef, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 hx1
  have hs0 : 0 < √x := by linarith
  have hxs : x = (√x) ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hε : 0 < (√x)⁻¹ := by positivity
  have hε1 : (√x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  set L := Real.log x with hLdef
  have hL4 : 4 ≤ L := WallsMeetRHVonKoch.four_le_log_of_le x hx
  have hL0 : 0 < L := by linarith
  have hLinv : L⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hLinv0 : 0 < L⁻¹ := inv_pos.2 hL0
  set σ₀ : ℝ := 1 + L⁻¹ with hσ₀def
  have hσ₀1 : 1 < σ₀ := by linarith
  have hσ₀2 : σ₀ ≤ 5 / 4 := by linarith
  -- the safe height `T ∈ [x, x + 1]`
  obtain ⟨T, ⟨hTx, hTx1⟩, hsafe⟩ := hCs x (by linarith)
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  -- the Mellin transform of the cutoff at scale `ε = x^(-1/2)`
  set M : ℂ → ℂ := mellin (fun y ↦ (TauCeti.smoothCutoff ν (√x)⁻¹ y : ℂ)) with hMdef
  have hMd : DifferentiableOn ℂ M {s : ℂ | 0 < s.re} :=
    TauCeti.differentiableOn_mellin_smoothCutoff hνs' hνi hε
  have hMan : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ M s := fun s hs ↦
    hMd.analyticAt (hopen.mem_nhds hs)
  have hMb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 →
      ‖M s‖ ≤ C / (‖s‖ * (1 + (√x)⁻¹ * ‖s‖)) := fun s h1 h2 ↦ hC _ hε hε1 s h1 h2
  have hMb' : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 → ‖M s‖ ≤ C / ‖s‖ := fun s h1 h2 ↦ by
    have hn : 0 < ‖s‖ :=
      lt_of_lt_of_le (by norm_num) (h1.trans ((le_abs_self _).trans (abs_re_le_norm s)))
    refine (hMb s h1 h2).trans (div_le_div_of_nonneg_left hC0 hn ?_)
    exact le_mul_of_one_le_right hn.le (le_add_of_nonneg_right (by positivity))
  have hpowan : ∀ s : ℂ, AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s := fun s ↦
    (differentiable_id.const_cpow (Or.inl hxC)).analyticAt s
  -- the zeros inside the rectangle, and the pole set
  set R : Set ℂ := Set.Ioo (1 / 4 : ℝ) σ₀ ×ℂ Set.Ioo (-T) T with hRdef
  set Z : Finset ℂ :=
    (TauCeti.riemannZetaZerosClosedBall 0 (T + 2)).filter (fun z ↦ z ∈ R) with hZdef
  have hZmem : ∀ z, z ∈ Z ↔ riemannZeta z = 0 ∧ z ∈ R := fun z ↦ by
    simp only [Z, Finset.mem_filter, TauCeti.mem_riemannZetaZerosClosedBall, sub_zero]
    constructor
    · rintro ⟨⟨-, h⟩, hR⟩; exact ⟨h, hR⟩
    · rintro ⟨h, hR⟩
      refine ⟨⟨?_, h⟩, hR⟩
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := mem_reProdIm.1 hR
      have h1 : |z.re| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
      have h2 : |z.im| ≤ T := abs_le.2 ⟨hi1.le, hi2.le⟩
      linarith [norm_le_abs_re_add_abs_im z]
  have hZre : ∀ z ∈ Z, z.re = 1 / 2 := fun z hz ↦ by
    obtain ⟨hζ, hR⟩ := (hZmem z).1 hz
    obtain ⟨⟨hr1, -⟩, -⟩ := mem_reProdIm.1 hR
    exact re_eq_half_of_zero (by linarith) (TauCeti.re_lt_one_of_riemannZeta_eq_zero hζ) hζ
  have h1Z : (1 : ℂ) ∉ Z := fun h ↦ riemannZeta_one_ne_zero ((hZmem 1).1 h).1
  set P : Finset ℂ := insert 1 Z with hPdef
  have hP : ∀ p ∈ P, p ∈ R := fun p hp ↦ by
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact mem_reProdIm.2 ⟨by simp only [one_re, Set.mem_Ioo]; constructor <;> linarith,
        by simp only [one_im, Set.mem_Ioo]; constructor <;> linarith⟩
    · exact ((hZmem p).1 hp).2
  -- the integrand
  set f : ℂ → ℂ := fun s ↦ (G s + 1 / (s - 1)) * M s * (x : ℂ) ^ s with hfdef
  have hreg : ∀ s ∈ Set.Icc (1 / 4 : ℝ) σ₀ ×ℂ Set.Icc (-T) T \ (P : Set ℂ),
      s ≠ 1 ∧ riemannZeta s ≠ 0 := fun s ⟨hs, hsP⟩ ↦ by
    have hs1 : s ≠ 1 := fun h ↦ hsP (by rw [h]; exact Finset.mem_coe.2 (Finset.mem_insert_self 1 Z))
    refine ⟨hs1, fun hζ ↦ hsP ?_⟩
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := mem_reProdIm.1 hs
    have hre : s.re < 1 := TauCeti.re_lt_one_of_riemannZeta_eq_zero hζ
    have hhalf : s.re = 1 / 2 := re_eq_half_of_zero (by linarith) hre hζ
    rcases lt_or_eq_of_le hi1 with hi1 | hi1
    · rcases lt_or_eq_of_le hi2 with hi2 | hi2
      · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem ((hZmem s).2
          ⟨hζ, mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, hi1, hi2⟩⟩))
      · exfalso
        refine (hsafe s.re (by linarith) (by linarith) s ?_).1 hζ
        rw [Set.mem_insert_iff, Set.mem_singleton_iff]
        left; apply Complex.ext <;> simp [hi2]
    · exfalso
      refine (hsafe s.re (by linarith) (by linarith) s ?_).1 hζ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; apply Complex.ext <;> simp [← hi1]
  have hdiff : ∀ s ∈ Set.Icc (1 / 4 : ℝ) σ₀ ×ℂ Set.Icc (-T) T \ (P : Set ℂ),
      DifferentiableAt ℂ f s := fun s hs ↦ by
    obtain ⟨hs1, hζ⟩ := hreg s hs
    have hre : 0 < s.re := by have := (mem_reProdIm.1 hs.1).1.1; linarith
    exact (((hGd s hζ).add ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.2 hs1))).mul (hMan s hre).differentiableAt).mul (hpowan s).differentiableAt
  have hc : ContinuousOn f (Set.Icc (1 / 4 : ℝ) σ₀ ×ℂ Set.Icc (-T) T \ (P : Set ℂ)) :=
    fun s hs ↦ (hdiff s hs).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℂ f (R \ (P : Set ℂ)) := fun s hs ↦
    (hdiff s ⟨⟨Set.Ioo_subset_Icc_self hs.1.1, Set.Ioo_subset_Icc_self hs.1.2⟩,
      hs.2⟩).differentiableWithinAt
  have hmer : ∀ p ∈ P, MeromorphicAt f p := fun p hp ↦ by
    have hre : 0 < p.re := by have := (mem_reProdIm.1 (hP p hp)).1.1; linarith
    have hpole : MeromorphicAt (fun s : ℂ ↦ (1 : ℂ) / (s - 1)) p := by fun_prop
    exact (((hGmer p).add hpole).mul (hMan p hre).meromorphicAt).mul (hpowan p).meromorphicAt
  -- the contour identity
  have hsum : LSeriesSummable (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ₀ :=
    TauCeti.LSeries.LSeriesSummable_of_norm_le_mul_log ha (by rw [ofReal_re]; linarith)
  have hre₀ (t : ℝ) : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
  have hL : ∀ t : ℝ, LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (σ₀ + t * I) =
      G (σ₀ + t * I) + 1 / (σ₀ + t * I - 1) := fun t ↦ hLG _ (by rw [hre₀]; exact hσ₀1)
  have hid := WallsMeetRHVonKoch.tsum_mul_smoothCutoff_eq_contour_add_sum_residue
    (a := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (G := G) (f := f) (r := 1) (P := P)
    hν1 hνs' hε hx0 (by norm_num : (0 : ℝ) < 1 / 4) (by linarith) hT0.le hsum hL (fun _ ↦ rfl)
    hP hc hd hmer
  -- the residues
  have hres1 : TauCeti.Contour.residue f 1 = M 1 * x := by
    rw [hfdef]
    have h := TauCeti.Contour.residue_add_div_sub_mul_of_analyticAt (r := (1 : ℂ)) hG1
      ((hMan 1 (by simp)).mul (hpowan 1))
    simpa only [Pi.mul_apply, mul_assoc, cpow_one, one_mul] using h
  have hresZ : ∀ ρ ∈ Z, ‖TauCeti.Contour.residue f ρ‖ ≤
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖ * (C * √x) := fun ρ hρ ↦ by
    obtain ⟨hζ, hR⟩ := (hZmem ρ).1 hρ
    have hρre := hZre ρ hρ
    have hρ1 : ρ ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hζ)
    have hH : AnalyticAt ℂ (fun z ↦ M z * (x : ℂ) ^ z) ρ :=
      (hMan ρ (by rw [hρre]; norm_num)).mul (hpowan ρ)
    have hF : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ,
        f z = -(logDeriv riemannZeta z) * (M z * (x : ℂ) ^ z) := by
      filter_upwards [WallsMeetRHVonKoch.riemannZeta_eventually_ne_zero hζ,
        (eventually_ne_nhds hρ1).filter_mono nhdsWithin_le_nhds] with z hz hz1
      show (G z + 1 / (z - 1)) * M z * (x : ℂ) ^ z = _
      rw [hGeq z hz1 hz, logDeriv_apply]
      ring
    rw [WallsMeetRHVonKoch.residue_neg_logDeriv_riemannZeta_mul hζ hH hF, norm_mul, norm_neg, Complex.norm_natCast,
      norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, hρre, ← Real.sqrt_eq_rpow]
    have hρn : 0 < ‖ρ‖ := lt_of_lt_of_le (by norm_num)
      ((by rw [hρre]; norm_num : (1 / 2 : ℝ) ≤ |ρ.re|).trans (abs_re_le_norm ρ))
    have hMρ := hMb' ρ (by rw [hρre]; norm_num) (by rw [hρre]; norm_num)
    calc ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (‖M ρ‖ * √x)
        ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (C / ‖ρ‖ * √x) := by gcongr
      _ = _ := by ring
  have hsumres : ‖∑ p ∈ Z, TauCeti.Contour.residue f p‖ ≤
      C * √x * (Cz * Real.log (T + 2) ^ 2) := by
    calc ‖∑ p ∈ Z, TauCeti.Contour.residue f p‖
        ≤ ∑ p ∈ Z, ((analyticOrderAt riemannZeta p).toNat : ℝ) / ‖p‖ * (C * √x) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hresZ)
      _ = (∑ p ∈ Z, ((analyticOrderAt riemannZeta p).toNat : ℝ) / ‖p‖) * (C * √x) := by
          rw [Finset.sum_mul]
      _ ≤ Cz * Real.log (T + 2) ^ 2 * (C * √x) := by
          gcongr
          refine hCz T hT1 Z fun z hz ↦ ⟨by rw [hZre z hz]; norm_num, by rw [hZre z hz]; norm_num,
            ((hZmem z).1 hz).1, ?_⟩
          obtain ⟨-, hi1, hi2⟩ := mem_reProdIm.1 ((hZmem z).1 hz).2
          exact abs_le.2 ⟨hi1.le, hi2.le⟩
      _ = _ := by ring
  -- the vertical tails
  have hLb : ∀ t : ℝ, T < |t| →
      ‖LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (σ₀ + t * I)‖ ≤ 8 * L ^ 2 :=
    fun t _ ↦ by
    have h := TauCeti.LSeries.norm_LSeries_le_of_norm_le_mul_log ha (s := (σ₀ : ℂ) + t * I)
      (by rw [hre₀]; exact hσ₀1) (by rw [hre₀]; linarith)
    rw [hre₀] at h
    refine h.trans (le_of_eq ?_)
    rw [hσ₀def, add_sub_cancel_left]
    field_simp
  have hxσ₀ : x ^ σ₀ ≤ Real.exp 1 * x := by
    rw [hσ₀def, Real.rpow_add hx0, Real.rpow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right Real.rpow_inv_log_le_exp_one hx0.le
  have htail : ‖∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)‖ ≤
      2 * (8 * L ^ 2 * C * (Real.exp 1 * x)) / ((√x)⁻¹ * T) := by
    refine TauCeti.norm_integral_vertical_tail_le (f := f) (σ := σ₀)
      (K := 8 * L ^ 2 * C * (Real.exp 1 * x)) hε hT0 fun t ht ↦ ?_
    have h := WallsMeetRHVonKoch.norm_mul_mul_cpow_le' (s := (σ₀ : ℂ) + t * I) hx0.le (hLb t ht)
      (hMb ((σ₀ : ℂ) + t * I) (by rw [hre₀]; linarith) (by rw [hre₀]; linarith))
    rw [hre₀] at h
    show ‖(G ((σ₀ : ℂ) + t * I) + 1 / ((σ₀ : ℂ) + t * I - 1)) * M ((σ₀ : ℂ) + t * I) *
      (x : ℂ) ^ ((σ₀ : ℂ) + t * I)‖ ≤ _
    rw [← hL t]
    exact h.trans (div_le_div_of_nonneg_right (by gcongr) (by positivity))
  -- the left edge `Re s = 1/4`
  have hleft : ‖∫ t in (-T)..T, f (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤
      4 * ((4 * C₁ * Real.log (T + 2) + 4 / 3) * C * x ^ (1 / 4 : ℝ)) *
        Real.log (1 + T / (1 / 4)) := by
    refine TauCeti.norm_intervalIntegral_vertical_le (f := f) (σ := 1 / 4)
      (K := (4 * C₁ * Real.log (T + 2) + 4 / 3) * C * x ^ (1 / 4 : ℝ)) (by norm_num) hT0.le
      fun t ht ↦ ?_
    set s : ℂ := ((1 / 4 : ℝ) : ℂ) + t * I with hsdef
    have hre : s.re = 1 / 4 := by simp [s]
    have him : s.im = t := by simp [s]
    have hs1 : s ≠ 1 := fun h ↦ by rw [h] at hre; norm_num at hre
    have hζ : riemannZeta s ≠ 0 :=
      WallsMeetRHVonKoch.riemannZeta_ne_zero_of_re_ne_half (by rw [hre]; norm_num) (by rw [hre]; norm_num)
    have hG : ‖G s + 1 / (s - 1)‖ ≤ 4 * C₁ * Real.log (T + 2) + 4 / 3 := by
      rw [show G s + 1 / (s - 1) = -(deriv riemannZeta s / riemannZeta s) by
        rw [hGeq s hs1 hζ]; ring, norm_neg]
      have h1 := hC₁ (1 / 4) (by norm_num) (by norm_num) s hs1 (by rw [hre])
        (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      have h2 : ‖1 / (s - 1)‖ ≤ 4 / 3 := by
        have : 3 / 4 ≤ ‖s - 1‖ := by
          have := abs_re_le_norm (s - 1)
          rw [sub_re, hre, one_re] at this
          norm_num at this
          linarith
        rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
        linarith
      have htri : ‖deriv riemannZeta s / riemannZeta s‖ ≤
          ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := by
        have := norm_sub_le (deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) (1 / (s - 1))
        rwa [add_sub_cancel_right] at this
      have hlog : Real.log (|s.im| + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by positivity) (by rw [him]; linarith [(abs_le.2 ht : |t| ≤ T)])
      have h3 : C₁ / (1 / 4) * Real.log (|s.im| + 2) ≤ 4 * C₁ * Real.log (T + 2) := by
        rw [show C₁ / (1 / 4) = 4 * C₁ by ring]
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith
    have h := WallsMeetRHVonKoch.norm_mul_mul_cpow_le' (s := s) hx0.le hG
      (hMb' s (by rw [hre]) (by rw [hre]; norm_num))
    rw [hre] at h
    exact h
  -- the horizontal edges `Im s = ±T`
  have hhoriz : ∀ τ : ℝ, |τ| = T → ‖∫ σ in (1 / 4 : ℝ)..σ₀, f (σ + τ * I)‖ ≤
      (σ₀ - 1 / 4) * (|Cs| * Real.log (x + 2) ^ 2 * C) * x ^ σ₀ / ((√x)⁻¹ * T ^ 2) := by
    intro τ hτ
    rw [← hτ, sq_abs]
    refine TauCeti.norm_intervalIntegral_horizontal_le (f := f)
      (K := |Cs| * Real.log (x + 2) ^ 2 * C) (by linarith)
      (fun h ↦ by rw [h, abs_zero] at hτ; linarith) hε hx1 fun σ hσ ↦ ?_
    set s : ℂ := (σ : ℂ) + τ * I with hsdef
    have hre : s.re = σ := by simp [s]
    have him : s.im = τ := by simp [s]
    have hτ0 : τ ≠ 0 := fun h ↦ by rw [h, abs_zero] at hτ; linarith
    have hs1 : s ≠ 1 := fun h ↦ hτ0 (by rw [← him, h, one_im])
    have hmem : s ∈ ({(σ : ℂ) + (T : ℂ) * I, (σ : ℂ) - (T : ℂ) * I} : Set ℂ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases (abs_eq hT0.le).1 hτ with h | h
      · left; rw [hsdef, h]
      · right; rw [hsdef, h]; push_cast; ring
    obtain ⟨hζ, hb⟩ := hsafe σ (by linarith [hσ.1]) (by linarith [hσ.2]) s hmem
    have hG : ‖G s + 1 / (s - 1)‖ ≤ |Cs| * Real.log (x + 2) ^ 2 := by
      rw [show G s + 1 / (s - 1) = -(deriv riemannZeta s / riemannZeta s) by
        rw [hGeq s hs1 hζ]; ring, norm_neg]
      exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have h := WallsMeetRHVonKoch.norm_mul_mul_cpow_le' (s := s) hx0.le hG
      (hMb s (by rw [hre]; exact hσ.1) (by rw [hre]; linarith [hσ.2]))
    rw [hre] at h
    exact h
  have htop := hhoriz T (abs_of_pos hT0)
  have hbot' : (∫ σ in (1 / 4 : ℝ)..σ₀, f (σ - T * I)) =
      ∫ σ in (1 / 4 : ℝ)..σ₀, f (σ + ((-T : ℝ) : ℂ) * I) :=
    intervalIntegral.integral_congr fun σ _ ↦ by simp [sub_eq_add_neg]
  have hbot := hhoriz (-T) (by rw [abs_neg, abs_of_pos hT0])
  rw [← hbot'] at hbot
  -- the sharp/smooth comparison and the main-term correction
  have hsm := TauCeti.norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le hν0' hνs' hνm hε hε1
    (X := x) (by linarith)
  have hmain := TauCeti.norm_mellin_smoothCutoff_one_sub_one_le hν0' hνs' hνm hε hε1
  set S := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
    TauCeti.smoothCutoff ν (√x)⁻¹ (n / x) with hSdef
  rw [Finset.sum_insert h1Z, hres1] at hid
  set E := (∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)) +
      (∫ t in (-T)..T, f (((1 / 4 : ℝ) : ℂ) + t * I)) +
      ((∫ σ in (1 / 4 : ℝ)..σ₀, f (σ + T * I)) - ∫ σ in (1 / 4 : ℝ)..σ₀, f (σ - T * I)) / I
    with hEdef
  have hE : ‖E‖ ≤ ‖∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)‖ +
      ‖∫ t in (-T)..T, f (((1 / 4 : ℝ) : ℂ) + t * I)‖ +
      (‖∫ σ in (1 / 4 : ℝ)..σ₀, f (σ + T * I)‖ + ‖∫ σ in (1 / 4 : ℝ)..σ₀, f (σ - T * I)‖) := by
    refine (norm_add₃_le).trans (add_le_add le_rfl ?_)
    rw [norm_div, norm_I, div_one]
    exact norm_sub_le _ _
  have hSM : S - M 1 * x = 1 / (2 * (Real.pi : ℂ)) * E + ∑ p ∈ Z, TauCeti.Contour.residue f p := by
    rw [hid]; ring
  have hπ : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  have hπ0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hSM' : ‖S - M 1 * x‖ ≤ 1 / (2 * Real.pi) *
      (2 * (8 * L ^ 2 * C * (Real.exp 1 * x)) / ((√x)⁻¹ * T) +
        4 * ((4 * C₁ * Real.log (T + 2) + 4 / 3) * C * x ^ (1 / 4 : ℝ)) *
          Real.log (1 + T / (1 / 4)) +
        ((σ₀ - 1 / 4) * (|Cs| * Real.log (x + 2) ^ 2 * C) * x ^ σ₀ / ((√x)⁻¹ * T ^ 2) +
          (σ₀ - 1 / 4) * (|Cs| * Real.log (x + 2) ^ 2 * C) * x ^ σ₀ / ((√x)⁻¹ * T ^ 2))) +
      C * √x * (Cz * Real.log (T + 2) ^ 2) := by
    rw [hSM]
    refine (norm_add_le _ _).trans (add_le_add ?_ hsumres)
    rw [norm_mul, hπ]
    refine mul_le_mul_of_nonneg_left (hE.trans ?_) hπ0
    exact add_le_add (add_le_add htail hleft) (add_le_add htop hbot)
  have hmt : ‖(M 1 - 1) * x‖ ≤ 2 * Real.log 2 * (√x)⁻¹ * x := by
    rw [norm_mul, Complex.norm_of_nonneg hx0.le]
    gcongr
  have hcast : |ψ x - x| = ‖(ψ x : ℂ) - (x : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdec : (ψ x : ℂ) - x = ((ψ x : ℂ) - S) + (S - M 1 * x) + (M 1 - 1) * x := by ring
  -- the logarithms
  have hlogsq : Real.log (x ^ 2) = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have hA0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hA2 : Real.log (T + 2) ≤ 2 * L := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hB0 : 0 ≤ Real.log (1 + T / (1 / 4)) := Real.log_nonneg (by
    have : 0 ≤ T / (1 / 4) := by positivity
    linarith)
  have hB2 : Real.log (1 + T / (1 / 4)) ≤ 2 * L := by
    rw [← hlogsq]
    refine Real.log_le_log (by positivity) ?_
    rw [show T / (1 / 4) = 4 * T by ring]
    nlinarith
  have hQ0 : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
  have hQ2 : Real.log (x + 2) ≤ 2 * L := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hq : x ^ (1 / 4 : ℝ) ≤ √x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hσ₀a : 0 ≤ σ₀ - 1 / 4 := by linarith
  have hσ₀b : σ₀ - 1 / 4 ≤ 1 := by linarith
  have hq0 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have hy0 : 0 ≤ x ^ σ₀ := by positivity
  have harith := vk_terms_le (σ₀ := σ₀) hC0 hC₁0 hCs0 hCz0 hs1 hxs hL4 hTx hA0 hA2 hB0 hB2 hQ0 hQ2
    hq0 hq (Real.exp_pos 1) hy0 hxσ₀ hσ₀a hσ₀b
  rw [hcast, hdec]
  calc ‖((ψ x : ℂ) - S) + (S - M 1 * x) + (M 1 - 1) * x‖
      ≤ ‖(ψ x : ℂ) - S‖ + ‖S - M 1 * x‖ + ‖(M 1 - 1) * x‖ := norm_add₃_le
    _ ≤ _ := by linarith

open scoped Chebyshev in
/-- **Von Koch's bound from the proved RH, with an explicit constant:**
`|ψ(x) - x| ≤ 21250000000 · √x log² x` for `x ≥ 55`. The numeral is
`16 e·168 + (64·33553 + 11)·168 + 8 e·5714987·168 + 4·168·4480 + 11 ≈ 2.124 × 10¹⁰`
(`e < 2.7182818286`). -/
theorem psi_sub_le_explicit : ∀ x : ℝ, 55 ≤ x →
    |ψ x - x| ≤ 21250000000 * √x * Real.log x ^ 2 := by
  obtain ⟨C, C₁, Cs, Cz, rfl, rfl, rfl, rfl, h⟩ := psi_sub_le_explicit_aux
  intro x hx
  refine (h x hx).trans ?_
  have he := Real.exp_one_lt_d9
  have hs : 0 ≤ √x * Real.log x ^ 2 := by positivity
  have ha1 : |(33413 : ℝ)| = 33413 := abs_of_nonneg (by norm_num)
  have ha2 : |(140 : ℝ)| = 140 := abs_of_nonneg (by norm_num)
  rw [ha1, ha2, abs_of_nonneg (by norm_num)]
  have hconst : 16 * Real.exp 1 * 168 + (64 * 33553 + 11) * 168 +
      8 * Real.exp 1 * (2 * 33413 + 288 * (140 : ℝ) ^ 2 + 24 * 140 + 1) * 168 +
      4 * 168 * (32 * 140) + 11 ≤ 21250000000 := by nlinarith
  calc _ = (16 * Real.exp 1 * 168 + (64 * 33553 + 11) * 168 +
        8 * Real.exp 1 * (2 * 33413 + 288 * (140 : ℝ) ^ 2 + 24 * 140 + 1) * 168 +
        4 * 168 * (32 * 140) + 11) * (√x * Real.log x ^ 2) := by ring
    _ ≤ 21250000000 * (√x * Real.log x ^ 2) := by gcongr
    _ = _ := by ring

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ 21250000006 · √x log² x` for `x ≥ 55` (`ψ - θ ≤ 6 √x log x`). -/
theorem theta_sub_le_explicit : ∀ x : ℝ, 55 ≤ x →
    |θ x - x| ≤ 21250000006 * √x * Real.log x ^ 2 := by
  intro x hx
  have hL4 := WallsMeetRHVonKoch.four_le_log_of_le x hx
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hL2 : Real.log x ≤ Real.log x ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) :=
        WallsMeetRHVonKoch.theta_sub_le_psi_sub_add x (by linarith)
    _ ≤ 21250000000 * √x * Real.log x ^ 2 + 6 * (√x * Real.log x ^ 2) := by
        gcongr
        exact psi_sub_le_explicit x hx
    _ = 21250000006 * √x * Real.log x ^ 2 := by ring

/-- `π(55) ≤ 56` (the prime count is a count below `56`). -/
theorem primeCounting_55_le : (Nat.primeCounting 55 : ℝ) ≤ 56 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting']
  exact_mod_cast Nat.count_le Nat.Prime (n := 55 + 1)

/-- `0 ≤ Li(55) ≤ 53 / log 2 ≤ 77`. -/
theorem logIntegral_55_le : 0 ≤ TauCeti.Real.logIntegral 55 ∧ TauCeti.Real.logIntegral 55 ≤ 77 := by
  refine ⟨TauCeti.Real.logIntegral_nonneg (by norm_num), ?_⟩
  have h := TauCeti.Real.integral_inv_log_pow_le 1 (a := 2) (b := 55) (by norm_num) (by norm_num)
  simp only [pow_one] at h
  rw [TauCeti.Real.logIntegral_def]
  refine h.trans ?_
  have := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `log 55 ≤ 5` (as `55 < e⁵`). -/
theorem log_55_le_five : Real.log 55 ≤ 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h0 := Real.exp_pos 1
  calc (55 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := by gcongr
    _ = Real.exp 5 := by rw [Real.exp_one_pow]; norm_num

open scoped Chebyshev in
/-- **`|π(⌊x⌋) - Li(x)| ≤ 913750000391 · √x log x` for `x ≥ 55`**, Tau Ceti's `θ → π` transfer
with `ε(t) = K t^(-1/2) log² t`, `K = 21250000006`: the boundary terms at `55` are
`|π(55) - Li 55| ≤ 56 + 77 = 133` and `K √55 log 55 ≤ 40 K`; the main terms are `K √x log x` and
`2 K √x log x`; `133 + 43 K = 913750000391`. -/
theorem primeCounting_sub_logIntegral_le_explicit : ∀ x : ℝ, 55 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤
      913750000391 * √x * Real.log x := by
  intro x hx
  obtain ⟨K, hKdef, hK⟩ : ∃ K : ℝ, K = 21250000006 ∧ ∀ x : ℝ, 55 ≤ x →
      |θ x - x| ≤ K * √x * Real.log x ^ 2 := ⟨_, rfl, theta_sub_le_explicit⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; norm_num
  set D1 := |(Nat.primeCounting ⌊(55 : ℝ)⌋₊ : ℝ) - TauCeti.Real.logIntegral 55| with hD1def
  set ε : ℝ → ℝ := fun t ↦ K * t ^ (-(1 / 2) : ℝ) * Real.log t ^ 2
  set D3 := 55 * ε 55 / Real.log 55 with hD3def
  have hl55 : 4 ≤ Real.log 55 := WallsMeetRHVonKoch.four_le_log_of_le 55 le_rfl
  have hD3 : 0 ≤ D3 := by simp only [D3, ε]; positivity
  have hD1 : 0 ≤ D1 := abs_nonneg _
  have hx0 : 0 < x := by linarith
  have hL4 := WallsMeetRHVonKoch.four_le_log_of_le x hx
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 (by linarith)
  have hsL : 1 ≤ √x * Real.log x := one_le_mul_of_one_le_of_one_le hs1 (by linarith)
  have hsL0 : 0 ≤ √x * Real.log x := by positivity
  have hεt (t : ℝ) (ht : 0 < t) : t * ε t = K * √t * Real.log t ^ 2 := by
    simp only [ε]
    have : t * t ^ (-(1 / 2) : ℝ) = √t := by
      rw [Real.sqrt_eq_rpow]
      calc t * t ^ (-(1 / 2) : ℝ) = t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_one]
        _ = t ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add ht _ _).symm
        _ = t ^ (1 / 2 : ℝ) := by norm_num
    rw [← this]; ring
  have hcontε : ContinuousOn ε (Set.uIcc 55 x) := by
    rw [Set.uIcc_of_le hx]
    refine (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
      fun t ht ↦ Or.inl (ne_of_gt (show (0 : ℝ) < t by linarith [ht.1])))).mul
      ((Real.continuousOn_log.mono fun t ht ↦ ?_).pow 2)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  have hint : IntervalIntegrable ε MeasureTheory.volume 55 x := hcontε.intervalIntegrable
  have hmain := Chebyshev.abs_primeCounting_sub_logIntegral_le (ε := ε) (x₀ := 55) (x := x)
    (by norm_num) hx hint (fun t ht ↦ by
      rw [hεt t (by linarith [ht.1])]; exact hK t ht.1)
  have h2 : x * ε x / Real.log x ≤ K * (√x * Real.log x) := by
    rw [hεt x hx0, div_le_iff₀ (by linarith)]; ring_nf; rfl
  have hcont : ContinuousOn (fun t ↦ ε t / Real.log t ^ 2) (Set.uIcc 55 x) := by
    rw [Set.uIcc_of_le hx] at hcontε ⊢
    refine hcontε.div ((Real.continuousOn_log.mono fun t ht ↦ ?_).pow 2) fun t ht ↦ ?_
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · have : 4 ≤ Real.log t := WallsMeetRHVonKoch.four_le_log_of_le t ht.1
      positivity
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ K * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 55 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have h4 : ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2 ≤ 2 * K * (√x * Real.log x) := by
    calc ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2
        ≤ ∫ t in (55 : ℝ)..x, K * t ^ (-(1 / 2) : ℝ) :=
          intervalIntegral.integral_mono_on hx hcont.intervalIntegrable hint2 fun t ht ↦ by
            have hlt : 4 ≤ Real.log t := WallsMeetRHVonKoch.four_le_log_of_le t ht.1
            simp only [ε]
            rw [div_le_iff₀ (by positivity)]
      _ = K * ((x ^ (-(1 / 2) + 1 : ℝ) - 55 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      _ ≤ K * (2 * √x) := by
          gcongr
          have h55 : (0 : ℝ) ≤ 55 ^ (-(1 / 2) + 1 : ℝ) := by positivity
          have hxh : x ^ (-(1 / 2) + 1 : ℝ) = √x := by
            rw [Real.sqrt_eq_rpow]; norm_num
          rw [hxh, div_le_iff₀ (by norm_num)]
          linarith
      _ ≤ 2 * K * (√x * Real.log x) := by
          have hsx : 0 ≤ √x := Real.sqrt_nonneg x
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.log x by linarith)
            (mul_nonneg hK0 hsx)]
  -- the boundary terms at `55`
  have hD1le : D1 ≤ 133 := by
    rw [hD1def, Nat.floor_ofNat]
    obtain ⟨hLi0, hLi⟩ := logIntegral_55_le
    have hπ := primeCounting_55_le
    have hπ0 : (0 : ℝ) ≤ (Nat.primeCounting 55 : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hD3le : D3 ≤ 40 * K := by
    have hl0 : 0 < Real.log 55 := by linarith
    have hD3' : D3 = K * √55 * Real.log 55 := by
      rw [hD3def, hεt 55 (by norm_num)]
      field_simp
    have hsq : √(55 : ℝ) ≤ 8 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [hD3']
    have := log_55_le_five
    have h0 : 0 ≤ K * √55 := mul_nonneg hK0 (Real.sqrt_nonneg _)
    calc K * √55 * Real.log 55 ≤ K * 8 * 5 := by gcongr
      _ = 40 * K := by ring
  change _ ≤ D1 + _ + D3 + _ at hmain
  have ha : D1 ≤ D1 * (√x * Real.log x) := le_mul_of_one_le_right hD1 hsL
  have hb : D3 ≤ D3 * (√x * Real.log x) := le_mul_of_one_le_right hD3 hsL
  have hc : D1 * (√x * Real.log x) ≤ 133 * (√x * Real.log x) :=
    mul_le_mul_of_nonneg_right hD1le hsL0
  have hd : D3 * (√x * Real.log x) ≤ 40 * K * (√x * Real.log x) :=
    mul_le_mul_of_nonneg_right hD3le hsL0
  subst hKdef
  have hgoal : (913750000391 : ℝ) * √x * Real.log x = 913750000391 * (√x * Real.log x) := by ring
  rw [hgoal]
  linarith

open Classical in
/-- **The walls meet RH with explicit constants.** For every `N ≥ 55` the wall count
`2 + #{n ≤ N that pass the wall test}` differs from `Li(N)` by at most `913750000391 √N log N`.
From `riemannHypothesis` (through `primeCounting_sub_logIntegral_le_explicit`) and Rayn-McLean's
`prime_count_walls`. -/
theorem walls_meet_rh_explicit : ∀ N : ℕ, 55 ≤ N →
    |((2 + ((Finset.range (N + 1)).filter WallsMeetRHVonKoch.passes).card : ℕ) : ℝ) -
      TauCeti.Real.logIntegral N| ≤ 913750000391 * √(N : ℝ) * Real.log (N : ℝ) := by
  intro N hN
  have h := primeCounting_sub_logIntegral_le_explicit N (by exact_mod_cast hN)
  rwa [Nat.floor_natCast, WallsMeetRHVonKoch.prime_count_walls N (by omega)] at h

end WallsMeetRHExplicit

#print axioms WallsMeetRHExplicit.norm_LFunctionTrivChar₁_one_le_pow_mul
#print axioms WallsMeetRHExplicit.count_zeros_disc_le
#print axioms WallsMeetRHExplicit.logDeriv_window_explicit
#print axioms WallsMeetRHExplicit.logDeriv_bound_explicit
#print axioms WallsMeetRHExplicit.exists_explicit_bump
#print axioms WallsMeetRHExplicit.riemannZeta_safe_height_of
#print axioms WallsMeetRHExplicit.sum_order_div_norm_le_of
#print axioms WallsMeetRHExplicit.psi_sub_le_explicit_aux
#print axioms WallsMeetRHExplicit.psi_sub_le_explicit
#print axioms WallsMeetRHExplicit.theta_sub_le_explicit
#print axioms WallsMeetRHExplicit.primeCounting_sub_logIntegral_le_explicit
#print axioms WallsMeetRHExplicit.walls_meet_rh_explicit

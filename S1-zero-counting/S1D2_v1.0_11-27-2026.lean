/-
Schoenfeld S1, part D2: Backlund's disc function and Jensen's count of its zeros.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the ported
goldbach-lean modules (SchoenfeldPort, Steve Hubbard, Apache-2.0), Mathlib 31ce06ea and Tau Ceti,
in the environment of the riemann-hypothesis-community repository (Lean v4.37.0-rc1). Apache-2.0.
-/
import SchoenfeldS1.D
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# Backlund's disc: the function `g`, its size, and Jensen's count

For Backlund's bound on `S(T)` one counts the zeros of `Re ζ(σ + iT)` on `1/2 ≤ σ ≤ 2`. These are
zeros of the analytic function

`gB T z = (ζ(z + iT) + ζ(z - iT))/2`,

which equals `Re ζ(σ + iT)` for real `z = σ` (`gB_eq_re_of_real`, by `ζ(conj s) = conj (ζ s)`).

* `norm_riemannZeta_le_on_disc'`: `‖ζ s‖ ≤ 8T + 48` for `‖s - (2 + iT)‖ ≤ 15/8`, `T ≥ 3`
  (the port's `norm_zeta_le`, `Re s ≥ 1/8`);
* `analyticOnNhd_gB`, `norm_gB_le`: `gB T` is analytic on the closed disc of radius `15/8` about
  `2` and bounded there by `8T + 48`;
* `norm_gB_two_ge`: `‖gB T 2‖ = |Re ζ(2 + iT)| ≥ 2 - π²/6`;
* `sum_divisor_gB_le` (**Jensen**, Mathlib's `AnalyticOnNhd.sum_divisor_le`): the zeros of `gB T`
  in the closed disc of radius `3/2` about `2`, with multiplicity, number at most
  `log((8T + 48)/(2 - π²/6)) / log(5/4)`;
* `card_le_sum_divisor`: any finite set of zeros of an analytic function in a closed disc, on which
  the function is not identically zero, has at most that many elements.

Numerically `1/log(5/4) = 4.4814...` and, for `T ≥ 14`, `log((8T + 48)/(2 - π²/6)) ≤ log T + 3.49`,
so the count is at most `4.49 log T + 15.6`; with the argument bookkeeping (`|S(T)| ≤ count + 3/2`,
S1D3, next chunk) this is the `RtB T = 4.5 log T + 17.1` of `SchoenfeldS1.F`.
-/

namespace SchoenfeldS1

open Complex Real Metric

local notation "ζ" => riemannZeta

/-- On the disc of radius `15/8` about `2 + iT`, `T ≥ 3`: `‖ζ s‖ ≤ 8T + 48`. -/
theorem norm_riemannZeta_le_on_disc' {T : ℝ} (hT : 3 ≤ T) {s : ℂ}
    (hs : ‖s - (2 + T * I)‖ ≤ 15 / 8) : ‖ζ s‖ ≤ 8 * T + 48 := by
  have hre : |(s - (2 + T * I)).re| ≤ 15 / 8 := (Complex.abs_re_le_norm _).trans hs
  have him : |(s - (2 + T * I)).im| ≤ 15 / 8 := (Complex.abs_im_le_norm _).trans hs
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at hre him
  norm_num at hre him
  rw [abs_le] at hre him
  have hsre : 1 / 8 ≤ s.re := by linarith [hre.1]
  have hsim : T - 15 / 8 ≤ s.im := by linarith [him.1]
  have h1 : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have e : (s - 1).im = s.im := by simp
    rw [e] at this
    linarith [le_abs_self s.im]
  have hb := SchoenfeldPort.PNTPort.ZetaZeros.norm_zeta_le (by linarith : 0 < s.re) h1
  have hn : ‖s‖ ≤ T + 23 / 4 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have a : |s.re| ≤ 31 / 8 := by rw [abs_le]; constructor <;> linarith [hre.1, hre.2]
    have b : |s.im| ≤ T + 15 / 8 := by rw [abs_le]; constructor <;> linarith [him.1, him.2]
    linarith
  have hdiv : ‖s‖ / s.re ≤ (T + 23 / 4) / (1 / 8) := by
    apply div_le_div₀ (by linarith) hn (by norm_num) hsre
  have : (T + 23 / 4) / (1 / 8) = 8 * T + 46 := by ring
  linarith

/-- Backlund's disc function `g(z) = (ζ(z + iT) + ζ(z - iT))/2`. -/
noncomputable def gB (T : ℝ) (z : ℂ) : ℂ := (ζ (z + T * I) + ζ (z - T * I)) / 2

lemma conj_add_mul_I (σ T : ℝ) : (starRingEnd ℂ) ((σ : ℂ) + T * I) = σ - T * I := by
  apply Complex.ext <;> simp

/-- For real `z = σ`, `gB T σ = Re ζ(σ + iT)`. -/
lemma gB_eq_re_of_real (T σ : ℝ) : gB T σ = ((ζ (σ + T * I)).re : ℂ) := by
  unfold gB
  rw [← conj_add_mul_I, riemannZeta_conj, Complex.add_conj]
  push_cast; ring

/-- `ζ(z - iT)` has the norm of `ζ(conj z + iT)`. -/
lemma norm_riemannZeta_sub_mul_I (T : ℝ) (z : ℂ) :
    ‖ζ (z - T * I)‖ = ‖ζ ((starRingEnd ℂ) z + T * I)‖ := by
  have e : z - T * I = (starRingEnd ℂ) ((starRingEnd ℂ) z + T * I) := by
    apply Complex.ext <;> simp; ring
  rw [e, riemannZeta_conj, Complex.norm_conj]

/-- `gB T` is analytic on the closed disc of radius `15/8` about `2`, for `T ≥ 3`. -/
theorem analyticOnNhd_gB {T : ℝ} (hT : 3 ≤ T) :
    AnalyticOnNhd ℂ (gB T) (closedBall 2 (15 / 8)) := by
  have hz1 : AnalyticOnNhd ℂ ζ (closedBall (2 + T * I) (15 / 8)) :=
    TauCeti.analyticOnNhd_riemannZeta_closedBall (by simp; rw [abs_of_pos (by linarith)]; linarith)
  have hz2 : AnalyticOnNhd ℂ ζ (closedBall (2 - T * I) (15 / 8)) :=
    TauCeti.analyticOnNhd_riemannZeta_closedBall (by simp; rw [abs_of_pos (by linarith)]; linarith)
  have h1 : AnalyticOnNhd ℂ (fun z => ζ (z + T * I)) (closedBall 2 (15 / 8)) := by
    refine hz1.comp (analyticOnNhd_id.add analyticOnNhd_const) ?_
    intro z hz
    have : z + T * I - (2 + T * I) = z - 2 := by ring
    simpa [mem_closedBall, dist_eq_norm, this] using hz
  have h2 : AnalyticOnNhd ℂ (fun z => ζ (z - T * I)) (closedBall 2 (15 / 8)) := by
    refine hz2.comp (analyticOnNhd_id.sub analyticOnNhd_const) ?_
    intro z hz
    have : z - T * I - (2 - T * I) = z - 2 := by ring
    simpa [mem_closedBall, dist_eq_norm, this] using hz
  show AnalyticOnNhd ℂ (fun z => (ζ (z + T * I) + ζ (z - T * I)) / 2) _
  exact (h1.add h2).div_const

/-- `‖gB T z‖ ≤ 8T + 48` on the closed disc of radius `15/8` about `2`, for `T ≥ 3`. -/
theorem norm_gB_le {T : ℝ} (hT : 3 ≤ T) {z : ℂ} (hz : z ∈ closedBall 2 (15 / 8)) :
    ‖gB T z‖ ≤ 8 * T + 48 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have ha : ‖ζ (z + T * I)‖ ≤ 8 * T + 48 := by
    apply norm_riemannZeta_le_on_disc' hT
    have : z + T * I - (2 + T * I) = z - 2 := by ring
    rw [this]; exact hz
  have hb : ‖ζ (z - T * I)‖ ≤ 8 * T + 48 := by
    rw [norm_riemannZeta_sub_mul_I]
    apply norm_riemannZeta_le_on_disc' hT
    have : (starRingEnd ℂ) z + T * I - (2 + T * I) = (starRingEnd ℂ) (z - 2) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_conj]; exact hz
  unfold gB
  rw [norm_div, Complex.norm_ofNat]
  have := norm_add_le (ζ (z + T * I)) (ζ (z - T * I))
  linarith [div_le_div_of_nonneg_right (this.trans (add_le_add ha hb)) (by norm_num : (0 : ℝ) ≤ 2)]

/-- `‖gB T 2‖ = |Re ζ(2 + iT)| ≥ 2 - π²/6`. -/
theorem norm_gB_two_ge (T : ℝ) : 2 - π ^ 2 / 6 ≤ ‖gB T 2‖ := by
  have e : gB T 2 = ((ζ (2 + T * I)).re : ℂ) := by
    have := gB_eq_re_of_real T 2
    simpa using this
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact (re_riemannZeta_two_add_ge T).trans (le_abs_self _)

lemma two_sub_pi_sq_div_six_pos : 0 < 2 - π ^ 2 / 6 := by
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

theorem gB_two_ne_zero (T : ℝ) : gB T 2 ≠ 0 := by
  intro h
  have := norm_gB_two_ge T
  rw [h, norm_zero] at this
  linarith [two_sub_pi_sq_div_six_pos]

/-- **Jensen's count for Backlund's disc.** For `T ≥ 3`, the zeros of `gB T` in the closed disc of
radius `3/2` about `2`, counted with multiplicity, number at most
`log((8T + 48)/(2 - π²/6)) / log(5/4)`. -/
theorem sum_divisor_gB_le {T : ℝ} (hT : 3 ≤ T) :
    ((∑ᶠ u, MeromorphicOn.divisor (gB T) (closedBall 2 (3 / 2)) u : ℤ) : ℝ) ≤
      Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4) := by
  have hM : (1 : ℝ) ≤ 8 * T + 48 := by linarith
  have h := AnalyticOnNhd.sum_divisor_le (c := (2 : ℂ)) (r := 3 / 2) (R := 15 / 8)
    (M := 8 * T + 48) (f := gB T) (by norm_num) (by norm_num) hM
    (by rw [abs_of_pos (by norm_num)]; exact analyticOnNhd_gB hT) (gB_two_ne_zero T)
    (fun z hz => norm_gB_le hT (by
      rw [abs_of_pos (by norm_num)] at hz; exact sphere_subset_closedBall hz))
  rw [abs_of_pos (by norm_num)] at h
  refine h.trans ?_
  have h54 : (0 : ℝ) < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have e : (15 / 8 : ℝ) / (3 / 2) = 5 / 4 := by norm_num
  rw [e]
  apply div_le_div_of_nonneg_right _ h54.le
  apply Real.log_le_log (div_pos (by linarith) (norm_pos_iff.mpr (gB_two_ne_zero T)))
  exact div_le_div_of_nonneg_left (by linarith) two_sub_pi_sq_div_six_pos (norm_gB_two_ge T)

/-- A finite set of zeros of an analytic function on a closed disc, on which the function does not
vanish identically (it is nonzero at the centre), has at most `∑ᶠ divisor` elements. -/
theorem card_le_sum_divisor {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hc : f c ≠ 0) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ closedBall c r ∧ f z = 0) :
    (s.card : ℤ) ≤ ∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u := by
  set D := MeromorphicOn.divisor f (closedBall c r)
  have hfin := D.finiteSupport (isCompact_closedBall c r)
  have hnn : ∀ u, 0 ≤ D u := fun u => by
    have h0 := Function.locallyFinsuppWithin.le_def.mp
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) u
    simpa using h0
  -- at a zero `z` in the disc the order is finite (else `f ≡ 0` on the connected disc) and `≥ 1`
  have hpos : ∀ z ∈ s, 1 ≤ D z := by
    intro z hz
    obtain ⟨hzd, hz0⟩ := hs z hz
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzd]
    have hfa := hf z hzd
    have hord : analyticOrderAt f z ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      have hpre : IsPreconnected (closedBall c r) := (convex_closedBall c r).isPreconnected
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hzd htop
      exact hc (this (mem_closedBall_self hr))
    have hne : analyticOrderAt f z ≠ 0 := hfa.analyticOrderAt_ne_zero.mpr hz0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord
    rw [← hn] at hne ⊢
    have : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; exact absurd (by simp) hne
      · exact h0
    simpa using this
  have hsub : s ⊆ hfin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    exact (lt_of_lt_of_le zero_lt_one (hpos z hz)).ne'
  rw [finsum_eq_sum_of_support_subset D (s := hfin.toFinset) (by simp)]
  calc (s.card : ℤ) = ∑ _z ∈ s, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ s, D z := Finset.sum_le_sum hpos
    _ ≤ ∑ z ∈ hfin.toFinset, D z := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => hnn z)

/-- **Backlund's zero count.** For `T ≥ 3`, any finite set of zeros of `gB T` in the closed disc of
radius `3/2` about `2` (in particular, of distinct zeros of `Re ζ(σ + iT)` with `1/2 ≤ σ ≤ 2`) has
at most `log((8T + 48)/(2 - π²/6)) / log(5/4)` elements. -/
theorem card_zeros_gB_le {T : ℝ} (hT : 3 ≤ T) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ closedBall 2 (3 / 2) ∧ gB T z = 0) :
    (s.card : ℝ) ≤ Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4) := by
  have h1 := card_le_sum_divisor (c := (2 : ℂ)) (r := 3 / 2) (by norm_num)
    ((analyticOnNhd_gB hT).mono (closedBall_subset_closedBall (by norm_num))) (gB_two_ne_zero T) s hs
  have h2 := sum_divisor_gB_le hT
  calc (s.card : ℝ) = ((s.card : ℤ) : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast h1
    _ ≤ _ := h2

end SchoenfeldS1

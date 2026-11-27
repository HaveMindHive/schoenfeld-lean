import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer

import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# The walls meet the proved Riemann hypothesis: von Koch's form (11-27-2026)

Companion of `WallsMeetRHSharp_v1.0_11-27-2026.lean`, same environment (the locally built
community proof of RH by Alpöge with Claude, Mathlib `31ce06ea`, Tau Ceti pinned). Every step is
kernel-checked.

* Turaq Rayn-McLean's wall count `prime_count_walls` (copied): for `N ≥ 3`,
  `π(N) = 2 + #{n ≤ N that pass the wall test}`.
* `psi_sub_le_sqrt_log_sq_of_RH`: `|ψ(x) - x| ≤ C √x log² x` (von Koch, 1901, under RH). The
  route is the truncated explicit formula: Tau Ceti's rectangle residue theorem on
  `[1/4, 1 + 1/log x] × [-T, T]` (`T ∈ [x, x + 1]` a safe height) for the smoothed Perron
  integrand `-(ζ′/ζ)(s) 𝓜χ_ε(s) xˢ`, `ε = x^(-1/2)`. The residues at the zeros `ρ` (all on
  `Re s = 1/2` by the proved RH) give `∑ m(ρ) 𝓜χ_ε(ρ) x^ρ`, bounded by `√x ∑ m(ρ)/|ρ| ≪ √x log² x`
  through the unit-window zero count; the left edge at `Re s = 1/4` is `O(x^(1/4) log² x)` since
  the zeros are at distance `≥ 1/4`; tails and horizontal edges are `O(√x log² x)`.
* `theta_sub_le_sqrt_log_sq_of_RH`, `primeCounting_sub_logIntegral_le_sqrt_log_of_RH`
  (`|π(⌊x⌋) - Li x| ≤ C √x log x`), `walls_meet_rh_sqrt_log` (`|W(N) - Li N| ≤ C √N log N`).

Two private lemmas of Tau Ceti (`finsum_subtype_riemannZeta_eq_sum` of `Window.lean` and
`nonneg_of_norm_mellin_smoothCutoff_le` of `ZeroFreeRegion.lean`) are copied in, and the proof of
`TauCeti.LSeries.tsum_mul_smoothCutoff_eq_residue_add_contour` is adapted (`Contour.lean`);
Tau Ceti is Apache-2.0, copyright The Tau Ceti contributors.
-/

open Complex

namespace WallsMeetRHVonKoch

/-! ## The wall count (Rayn-McLean), copied from `WallsMeetRH_v1.0_11-27-2026.lean` -/

theorem wing_identity (k kr f fr : ℤ) (hfr : fr * fr = 1) :
    6 * k + f = 6 * (k - f * fr * kr) + f * fr * (6 * kr + fr) := by
  linear_combination (-f) * hfr

theorem wing_closed (k kr f fr : ℤ) (hfr : fr * fr = 1) (hc : IsCoprime (6 * kr + fr) 6) :
    (6 * kr + fr) ∣ (6 * k + f) ↔ (6 * kr + fr) ∣ (k - f * fr * kr) := by
  have key := wing_identity k kr f fr hfr
  constructor
  · intro h
    have h1 : (6 * kr + fr) ∣ f * fr * (6 * kr + fr) := dvd_mul_left _ _
    have h2 : (6 * kr + fr) ∣ (6 * k + f) - f * fr * (6 * kr + fr) := dvd_sub h h1
    have h3 : (6 * kr + fr) ∣ (k - f * fr * kr) * 6 := by
      have : (6 * k + f) - f * fr * (6 * kr + fr) = (k - f * fr * kr) * 6 := by rw [key]; ring
      rw [this] at h2; exact h2
    exact hc.dvd_of_dvd_mul_right h3
  · intro h
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right h 6) (dvd_mul_left _ _)

theorem prime_seat (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  by_contra h
  have h23 : 2 ∣ q ∨ 3 ∣ q := by omega
  rcases h23 with h2 | h3
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 h2); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 h3); omega

theorem wall_walk_seat (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (p : ℤ) = 6 * k + f := by
  rcases prime_seat p hp h5 with h | h
  · exact ⟨(p : ℤ) / 6, 1, Or.inl rfl, by omega⟩
  · exact ⟨(p : ℤ) / 6 + 1, -1, Or.inr rfl, by omega⟩

theorem seat_coprime (j g : ℤ) (hg : g = 1 ∨ g = -1) : IsCoprime (6 * j + g) 6 := by
  rcases hg with rfl | rfl
  · exact ⟨1, -j, by ring⟩
  · exact ⟨-1, j, by ring⟩

/-- His wall formula: a seat `n = 6k + f` (`f = ±1`, `n ≥ 5`) is prime exactly when no block
`6j + g` (`j ≥ 1`, `g = ±1`) with `(6j + g)^2 ≤ n` divides `k - f g j`. -/
theorem wall_formula (k f : ℤ) (hf : f = 1 ∨ f = -1) (n : ℕ) (hn : (n : ℤ) = 6 * k + f)
    (h5 : 5 ≤ n) :
    n.Prime ↔ ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n →
      ¬ (6 * j + g) ∣ k - f * g * j := by
  constructor
  · intro hp j g hj hg hsq hd
    have hgg : g * g = 1 := by rcases hg with rfl | rfl <;> norm_num
    have h1 : (6 * j + g) ∣ (n : ℤ) := by
      rw [hn]; exact (wing_closed k j f g hgg (seat_coprime j g hg)).2 hd
    have hpos : 5 ≤ 6 * j + g := by rcases hg with rfl | rfl <;> omega
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = 6 * j + g :=
      ⟨(6 * j + g).toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [← ht] at h1 hsq hpos
    have h2 : t ∣ n := Int.natCast_dvd_natCast.1 h1
    have hsq' : t * t ≤ n := by exact_mod_cast hsq
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · omega
    · subst h; have : 5 ≤ t := by exact_mod_cast hpos
      nlinarith
  · intro hall
    by_contra hnp
    have hn0 : 0 < n := by omega
    set m := n.minFac with hm
    have hmp : m.Prime := Nat.minFac_prime (by omega)
    have hmd : m ∣ n := Nat.minFac_dvd n
    have hsq : m ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
    have hm2 : m ≠ 2 := by intro h; rw [h] at hmd; omega
    have hm3 : m ≠ 3 := by intro h; rw [h] at hmd; omega
    have hm5 : 5 ≤ m := by
      have := hmp.two_le
      rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with h | h | h | h
      · exact absurd h hm2
      · exact absurd h hm3
      · rw [h] at hmp; exact absurd hmp (by decide)
      · exact h
    have hseat := prime_seat m hmp hm5
    set j : ℤ := ((m : ℤ) + 1) / 6 with hj
    set g : ℤ := (m : ℤ) - 6 * j with hgdef
    have hg : g = 1 ∨ g = -1 := by rcases hseat with h | h <;> omega
    have hgg : g * g = 1 := by rcases hg with h | h <;> rw [h] <;> norm_num
    have hme : (m : ℤ) = 6 * j + g := by omega
    have hj1 : 1 ≤ j := by omega
    have hdz : (6 * j + g) ∣ 6 * k + f := by
      rw [← hme, ← hn]; exact Int.natCast_dvd_natCast.2 hmd
    have hd := (wing_closed k j f g hgg (seat_coprime j g hg)).1 hdz
    refine hall j g hj1 hg ?_ hd
    rw [← hme]; exact_mod_cast (by nlinarith : m * m ≤ n)

/-- The wall test: `n ≥ 5` is a seat `6k + f` whose wall `k` is closed by no block `6j + g`
with `(6j + g)^2 ≤ n`. -/
def passes (n : ℕ) : Prop := 5 ≤ n ∧ ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (n : ℤ) = 6 * k + f ∧
  ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n →
    ¬ (6 * j + g) ∣ k - f * g * j

theorem prime_iff_passes (n : ℕ) : n.Prime ↔ n = 2 ∨ n = 3 ∨ passes n := by
  constructor
  · intro hp
    have h2 := hp.two_le
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h; norm_num at hp
    · right; right
      obtain ⟨k, f, hf, hn⟩ := wall_walk_seat n hp h
      exact ⟨h, k, f, hf, hn, (wall_formula k f hf n hn h).1 hp⟩
  · rintro (rfl | rfl | ⟨h5, k, f, hf, hn, ht⟩)
    · norm_num
    · norm_num
    · exact (wall_formula k f hf n hn h5).2 ht

open Classical in
/-- His wall count: for `N ≥ 3`, the number of primes up to `N` is `2` (the two mirrors)
plus the number of `n ≤ N` that pass the wall test. -/
theorem prime_count_walls (N : ℕ) (hN : 3 ≤ N) :
    Nat.primeCounting N = 2 + ((Finset.range (N + 1)).filter passes).card := by
  have h0 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [h0]
  have h1 : (Finset.range (N + 1)).filter Nat.Prime =
      (Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3) ∪
        (Finset.range (N + 1)).filter passes := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr (fun n _ => by rw [prime_iff_passes]; tauto)
  have h2 : (Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3) = {2, 3} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h3 : Disjoint ((Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3))
      ((Finset.range (N + 1)).filter passes) := by
    rw [Finset.disjoint_filter]
    rintro n _ (rfl | rfl) ⟨h5, -⟩ <;> omega
  rw [h1, Finset.card_union_of_disjoint h3, h2, Finset.card_pair (by norm_num)]


/-! ## Copied from `WallsMeetRHSharp`: RH consequences, Tau Ceti private lemmas, small facts -/

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

/-- Copy of a private lemma of Tau Ceti's `ZeroFreeRegion.lean` (Apache 2.0): the Mellin bound at
`ε = 1`, `s = 1` forces `C ≥ 0`. -/
theorem nonneg_of_norm_mellin_smoothCutoff_le' {ν : ℝ → ℝ} {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (TauCeti.smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    0 ≤ C := by
  have h := hC 1 one_pos le_rfl 1 (by norm_num) (by norm_num)
  rw [norm_one, one_mul, mul_one] at h
  exact (div_nonneg_iff.1 ((norm_nonneg _).trans h)).elim (·.1) fun h' ↦ absurd h'.2 (by norm_num)

/-- For `x ≥ 55`, `log x ≥ 4` (as `e⁴ < 55`). -/
theorem four_le_log_of_le (x : ℝ) (hx : 55 ≤ x) : 4 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [Real.exp_one_pow]; norm_num
    _ ≤ 2.7182818286 ^ 4 := by gcongr
    _ ≤ 55 := by norm_num
    _ ≤ x := hx

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ |ψ(x) - x| + 6 √x log x` for `x ≥ 3` (Tau Ceti's `ψ - θ` bound). -/
theorem theta_sub_le_psi_sub_add (x : ℝ) (hx : 3 ≤ x) :
    |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl4b : Real.log 4 ≤ 2 := by rw [hl4]; linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := by rw [hl4]; positivity
  have hL : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 (by linarith [Real.exp_one_lt_d9])
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have h := Chebyshev.abs_theta_sub_le_abs_psi_sub_add (c := Real.log 4)
    (fun y hy ↦ Chebyshev.theta_le_log4_mul_x hy.le) hx0.le
  have hcube : x ^ ((1 : ℝ) / 3) ≤ √x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hmax : max (Real.log x / Real.log 2 - 2) 0 ≤ Real.log x / Real.log 2 :=
    max_le (by linarith) (by positivity)
  have hprod : max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) ≤
      Real.log x / Real.log 2 * √x :=
    mul_le_mul hmax hcube (by positivity) (by positivity)
  have h1 : Real.log 4 * √x ≤ 2 * (√x * Real.log x) := by
    calc Real.log 4 * √x ≤ 2 * √x := mul_le_mul_of_nonneg_right hl4b hs0
      _ ≤ 2 * (√x * Real.log x) := by nlinarith
  have h2 : Real.log 4 * (Real.log x / Real.log 2 * √x) = 2 * (√x * Real.log x) := by
    rw [hl4]; field_simp
  have h3 := mul_le_mul_of_nonneg_left hprod hl40
  have h0 : 0 ≤ √x * Real.log x := by positivity
  nlinarith

/-! ## `ζ′/ζ` at distance `a` from the critical line, on `-1 ≤ Re s ≤ 2` -/

/-- From the proved `riemannHypothesis`: `ζ(s) ≠ 0` when `-2 < Re s` and `Re s ≠ 1/2`. -/
theorem riemannZeta_ne_zero_of_re_ne_half {s : ℂ} (hs : -2 < s.re) (hh : s.re ≠ 1 / 2) :
    riemannZeta s ≠ 0 := by
  intro h0
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero h0
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    linarith [n.cast_nonneg (α := ℝ)]
  exact hh (riemannHypothesis s h0 htriv hs1)

/-- **Under the proved RH, `ζ′/ζ + 1/(s - 1)` is `O(log(|Im s| + 2) / a)` at horizontal distance
`a` from the critical line**, on `-1 ≤ Re s ≤ 2`, with one absolute constant for every
`a ∈ (0, 1]`. -/
theorem logDeriv_bound_of_RH_dist : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, s ≠ 1 →
    -1 ≤ s.re → s.re ≤ 2 → a ≤ |s.re - 1 / 2| →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C / a * Real.log (|s.im| + 2) := by
  classical
  obtain ⟨Cw, hCw⟩ := TauCeti.riemannZeta_logDeriv_window
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨|Cw| + |Cc|, by positivity, fun a ha ha1 s hs1 hs hs2 hd ↦ ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg t])
  have hζ : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_re_ne_half (by linarith) fun h ↦ by rw [h, sub_self, abs_zero] at hd; linarith
  have hw := hCw s hs hs2 hs1 hζ
  set m : ℂ → ℕ := fun z ↦ (analyticOrderAt riemannZeta z).toNat
  set Z := TauCeti.riemannZetaZerosClosedBall (2 + t * I) 4
  rw [← ht, TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall t
    fun z ↦ (m z : ℂ) / (s - z)] at hw
  set W := ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0,
    (m z : ℂ) / (s - z)
  have hcount : ∑ z ∈ Z, (m z : ℝ) ≤ Cc * L := by
    have h := hCc (2 + t * I) (by simp)
    rwa [finsum_subtype_riemannZeta_eq_sum' (2 + t * I) 4 fun z ↦ (m z : ℝ),
      show (2 + t * I).im = t by simp] at h
  have hW : ‖W‖ ≤ Cc * L / a := by
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
      _ ≤ Cc * L / a := by gcongr
  set H := deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
  have htri : ‖H‖ ≤ ‖H - W‖ + ‖W‖ := by
    have := norm_add_le (H - W) W
    rwa [sub_add_cancel] at this
  have h1 : Cw * L ≤ |Cw| * L / a :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hL).trans (le_div_self (by positivity) ha ha1)
  have h2 : Cc * L / a ≤ |Cc| * L / a := by gcongr; exact le_abs_self _
  calc ‖H‖ ≤ Cw * L + Cc * L / a := by linarith
    _ ≤ |Cw| * L / a + |Cc| * L / a := add_le_add h1 h2
    _ = (|Cw| + |Cc|) / a * L := by ring

/-! ## The residue of `-(ζ′/ζ) · H` at a zero of `ζ` -/

/-- Near a zero `ρ` of `ζ`, `ζ ≠ 0` on a punctured neighbourhood (the zeros are isolated, the
analytic order at `ρ` being finite). -/
theorem riemannZeta_eventually_ne_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, riemannZeta z ≠ 0 := by
  have hρ1 : ρ ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hρ)
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have htop : analyticOrderAt riemannZeta ρ = ⊤ := analyticOrderAt_eq_top.mpr h
    have := TauCeti.one_le_toNat_analyticOrderAt_riemannZeta hρ
    rw [htop] at this
    simp at this
  · exact h

/-- **The residue of `-(ζ′/ζ) · H` at a zero `ρ` of `ζ` is `-m(ρ) H(ρ)`**, `m(ρ)` the analytic
order, for `H` analytic at `ρ` and any `F` agreeing with `-(logDeriv ζ) · H` near `ρ`. -/
theorem residue_neg_logDeriv_riemannZeta_mul {ρ : ℂ} (hρ : riemannZeta ρ = 0) {H F : ℂ → ℂ}
    (hH : AnalyticAt ℂ H ρ)
    (hF : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, F z = -(logDeriv riemannZeta z) * H z) :
    TauCeti.Contour.residue F ρ =
      -(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) * H ρ := by
  have hρ1 : ρ ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hρ)
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  set m : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hm
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    have := TauCeti.one_le_toNat_analyticOrderAt_riemannZeta hρ
    rw [htop] at this
    simp at this
  have hord : meromorphicOrderAt riemannZeta ρ = ((m : ℤ) : WithTop ℤ) := by
    rw [han.meromorphicOrderAt_eq, ← ENat.natCast_toNat hfin, ENat.map_natCast]
  obtain ⟨g, hg, hg0, hlog⟩ :=
    TauCeti.Contour.logDeriv_eventuallyEq_principalPart han.meromorphicAt hord
  have hφ : AnalyticAt ℂ (fun z ↦ -(((m : ℤ) : ℂ) * H z + (z - ρ) * logDeriv g z * H z)) ρ := by
    have := hg.logDeriv hg0
    fun_prop
  rw [TauCeti.Contour.residue_eq_of_eventuallyEq_div_sub hφ ?_]
  · simp
  filter_upwards [hF, hlog, self_mem_nhdsWithin] with z hz1 hz2 hz3
  have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hz3
  rw [hz1, hz2]
  field_simp

/-! ## `∑ m(ρ)/|ρ|` over the zeros up to height `T` is `O(log² T)` -/

/-- For `T ≥ 1`, `1 ≤ log (T + 2)`. -/
theorem one_le_log_add_two {T : ℝ} (hT : 1 ≤ T) : 1 ≤ Real.log (T + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- The half-plane case: the zeros of `ζ` in a finite set `P` with `1/4 ≤ Re z ≤ 1` and
`0 ≤ σ Im z ≤ T` (`σ = ±1`) satisfy `∑_{z ∈ P} m(z)/‖z‖ ≤ 4 |Cc| log(T + 2) (1 + log(T + 1))`,
`Cc` the window-count constant. Grouping by `⌊σ Im z⌋`, each group lies in a disc of radius `4`
about `2 + iσk` and has `‖z‖ ≥ max(1/4, k)`, so `1/‖z‖ ≤ 4/(k + 1)`; the harmonic sum closes. -/
theorem sum_order_div_norm_le_half {Cc : ℝ}
    (hCc : ∀ s₀ : ℂ, s₀.re = 2 →
      ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℝ) ≤ Cc * Real.log (|s₀.im| + 2))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 1 ≤ T) (P : Finset ℂ)
    (hP : ∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ 0 ≤ σ * z.im ∧ σ * z.im ≤ T) :
    ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤
      4 * |Cc| * Real.log (T + 2) * (1 + Real.log (T + 1)) := by
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
  -- each fibre
  have hfib : ∀ k ∈ Finset.range (N + 1),
      ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖ ≤
        4 * |Cc| * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ := fun k hk ↦ by
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    -- the fibre lies in the disc of radius `4` about `2 + iσk`
    have hsub : P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k) ⊆
        TauCeti.riemannZetaZerosClosedBall (2 + ((σ * k : ℝ) : ℂ) * I) 4 := fun z hz ↦ by
      obtain ⟨hzP, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3, h4⟩ := hP z hzP
      have hfl := Nat.floor_le h3
      have hfl' := Nat.lt_floor_add_one (σ * z.im)
      rw [hzk] at hfl hfl'
      refine TauCeti.mem_riemannZetaZerosClosedBall_two_add (abs_le.2 ⟨by linarith, by linarith⟩)
        ?_ hζ
      have : z.im - σ * k = σ * (σ * z.im - k) := by linear_combination (-z.im) * hσσ
      rw [this, abs_mul, hσabs, one_mul]
      exact (abs_le.2 ⟨by linarith, by linarith⟩ : |σ * z.im - k| ≤ 1).trans (by norm_num)
    -- `1/‖z‖ ≤ 4/(k + 1)` on the fibre
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
    have hcount : ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z ≤ |Cc| * Real.log (T + 2) := by
      have h := hCc (2 + ((σ * k : ℝ) : ℂ) * I) (by simp)
      rw [finsum_subtype_riemannZeta_eq_sum' _ 4 m,
        show (2 + ((σ * k : ℝ) : ℂ) * I).im = σ * k by simp, abs_mul, hσabs, one_mul,
        abs_of_nonneg hk0] at h
      have hk' : (k : ℝ) ≤ T := by
        have : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact this.trans (Nat.floor_le (by linarith))
      calc ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z
          ≤ ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + ((σ * k : ℝ) : ℂ) * I) 4, m z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
        _ ≤ Cc * Real.log ((k : ℝ) + 2) := h
        _ ≤ |Cc| * Real.log (T + 2) := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ k + 2 by linarith)
            calc Cc * Real.log ((k : ℝ) + 2) ≤ |Cc| * Real.log ((k : ℝ) + 2) := by
                  gcongr; exact le_abs_self _
              _ ≤ |Cc| * Real.log (T + 2) := by gcongr
    calc ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖
        ≤ ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z * (4 * ((k : ℝ) + 1)⁻¹) := by
          refine Finset.sum_le_sum fun z hz ↦ ?_
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (hnorm z hz) (by positivity)
      _ = (∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z) * (4 * ((k : ℝ) + 1)⁻¹) := by
          rw [Finset.sum_mul]
      _ ≤ |Cc| * Real.log (T + 2) * (4 * ((k : ℝ) + 1)⁻¹) := by gcongr
      _ = _ := by ring
  -- the harmonic sum
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
      ≤ ∑ k ∈ Finset.range (N + 1), 4 * |Cc| * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ :=
        Finset.sum_le_sum hfib
    _ = 4 * |Cc| * Real.log (T + 2) * ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 4 * |Cc| * Real.log (T + 2) * (1 + Real.log (T + 1)) := by gcongr

/-- **`∑ m(ρ)/|ρ| ≤ C log²(T + 2)` over any finite set of zeros of `ζ` with `1/4 ≤ Re ρ ≤ 1` and
`|Im ρ| ≤ T`**, `T ≥ 1`. -/
theorem sum_order_div_norm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ P : Finset ℂ,
    (∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ |z.im| ≤ T) →
    ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤ C * Real.log (T + 2) ^ 2 := by
  classical
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨16 * |Cc|, by positivity, fun T hT P hP ↦ ?_⟩
  have hup := sum_order_div_norm_le_half hCc (Or.inl rfl) hT (P.filter fun z ↦ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by simpa using h0, by rw [one_mul]; exact (le_abs_self _).trans h3⟩
  have hdn := sum_order_div_norm_le_half hCc (Or.inr rfl) hT (P.filter fun z ↦ ¬ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by rw [neg_one_mul]; linarith [not_le.mp h0], by
        rw [neg_one_mul]; exact (neg_le_abs _).trans h3⟩
  rw [← Finset.sum_filter_add_sum_filter_not P fun z ↦ 0 ≤ z.im]
  have hl1 : 1 ≤ Real.log (T + 2) := one_le_log_add_two hT
  have hl2 : Real.log (T + 1) ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
  have hC0 : 0 ≤ |Cc| := abs_nonneg _
  nlinarith [mul_nonneg hC0 (sub_nonneg.2 hl1), mul_nonneg hC0 (sub_nonneg.2 hl2),
    mul_nonneg (mul_nonneg hC0 (sub_nonneg.2 hl1)) (sub_nonneg.2 hl2)]

/-! ## The smoothed sum as contour terms plus residues at a finite pole set -/

open MeasureTheory Filter Set in
/-- **Tau Ceti's contour identity with a finite pole set** (adapted from
`TauCeti.LSeries.tsum_mul_smoothCutoff_eq_residue_add_contour`, Apache 2.0). For `x > 0`,
`0 < σ₁ ≤ σ₀`, `T ≥ 0`, the L-series of `a` summable at `σ₀` and equal to `G(s) + r/(s - 1)` on the
line `Re s = σ₀`, and `f(s) = (G(s) + r/(s - 1)) · mellin χ_ε s · xˢ` continuous on the closed
rectangle off `P`, differentiable on the open rectangle off `P` and meromorphic at each point of
`P ⊆` open rectangle: the smoothed sum is `(2π)⁻¹` times the tails, left edge and horizontal
term, plus `∑_{p ∈ P} residue f p`. -/
theorem tsum_mul_smoothCutoff_eq_contour_add_sum_residue {ν : ℝ → ℝ} {ε : ℝ} {a : ℕ → ℂ}
    {G f : ℂ → ℂ} {r : ℂ} {x σ₀ σ₁ T : ℝ} {P : Finset ℂ} (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) (hx : 0 < x)
    (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₀) (hT : 0 ≤ T)
    (hs : LSeriesSummable a σ₀)
    (hL : ∀ t : ℝ, LSeries a (σ₀ + t * I) = G (σ₀ + t * I) + r / (σ₀ + t * I - 1))
    (hf : ∀ s, f s =
      (G s + r / (s - 1)) * mellin (fun y ↦ (TauCeti.smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s)
    (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₀ ×ℂ Ioo (-T) T)
    (hc : ContinuousOn f (Icc σ₁ σ₀ ×ℂ Icc (-T) T \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p) :
    ∑' n, a n * TauCeti.smoothCutoff ν ε (n / x) =
      (1 / (2 * Real.pi)) * ((∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)) +
          (∫ t in (-T)..T, f (σ₁ + t * I)) +
          ((∫ σ in σ₁..σ₀, f (σ + T * I)) - ∫ σ in σ₁..σ₀, f (σ - T * I)) / I) +
        ∑ p ∈ P, TauCeti.Contour.residue f p := by
  have hσ₀ : 0 < σ₀ := hσ₁.trans_le hσ
  obtain rfl : f = _ := funext hf
  have hline (t : ℝ) : (LSeries a (σ₀ + t * I) *
      mellin (fun y ↦ (TauCeti.smoothCutoff ν ε y : ℂ)) (σ₀ + t * I)) *
        (x : ℂ) ^ ((σ₀ : ℂ) + t * I) =
      (G (σ₀ + t * I) + r / (σ₀ + t * I - 1)) *
        mellin (fun y ↦ (TauCeti.smoothCutoff ν ε y : ℂ)) (σ₀ + t * I) *
          (x : ℂ) ^ ((σ₀ : ℂ) + t * I) := by
    rw [hL]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hint := ((TauCeti.LSeries.integrable_LSeries_mul_mellin_smoothCutoff a hν hνs hε hσ₀).mul_bdd
    (Continuous.aestronglyMeasurable (by fun_prop)) (c := x ^ σ₀)
    (Eventually.of_forall fun t ↦ by simp [norm_cpow_eq_rpow_re_of_pos hx])).congr
    (Eventually.of_forall hline)
  have hshift := TauCeti.Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue
    (P := P) hσ hT hP hc hd hmer hint
  have hcpow (t : ℝ) : ((x⁻¹ : ℝ) : ℂ) ^ (-((σ₀ : ℂ) + t * I)) = (x : ℂ) ^ ((σ₀ : ℂ) + t * I) := by
    rw [ofReal_inv, inv_cpow _ _ (by simp [arg_ofReal_of_nonneg hx.le, Real.pi_ne_zero.symm]),
      cpow_neg, inv_inv]
  rw [(TauCeti.LSeries.hasSum_mul_smoothCutoff hν hνs hε hσ₀ hs hx).tsum_eq, mellinInv, real_smul]
  simp only [smul_eq_mul, hcpow]
  rw [integral_congr_ae (Eventually.of_forall fun t ↦ (mul_comm _ _).trans (hline t)), hshift]
  have key : ∀ A B C D : ℂ, ((1 / (2 * Real.pi) : ℝ) : ℂ) * (A + B + C / I + 2 * (Real.pi : ℂ) * D) =
      1 / (2 * Real.pi) * (A + B + C / I) + D := by
    intro A B C D
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  exact key _ _ _ _

/-! ## von Koch: `|ψ(x) - x| ≤ C √x log² x` -/

/-- Copy of Tau Ceti's private `norm_mul_mul_cpow_le` (`ContourEstimate.lean`, Apache 2.0): if
`‖g‖ ≤ A` and `‖m‖ ≤ C / D`, then `‖g · m · xˢ‖ ≤ A C x^{Re s} / D` for `x ≥ 0`. -/
theorem norm_mul_mul_cpow_le' {g m s : ℂ} {A C D x : ℝ} (hx : 0 ≤ x) (hg : ‖g‖ ≤ A)
    (hm : ‖m‖ ≤ C / D) : ‖g * m * (x : ℂ) ^ s‖ ≤ A * C * x ^ s.re / D := by
  have hA : 0 ≤ A := (norm_nonneg g).trans hg
  have hCD : 0 ≤ C / D := (norm_nonneg m).trans hm
  have hp : ‖(x : ℂ) ^ s‖ ≤ x ^ s.re := by
    simpa [arg_ofReal_of_nonneg hx, abs_of_nonneg hx] using norm_cpow_le (x : ℂ) s
  rw [norm_mul, norm_mul]
  calc ‖g‖ * ‖m‖ * ‖(x : ℂ) ^ s‖ ≤ A * (C / D) * x ^ s.re := by gcongr
    _ = A * C * x ^ s.re / D := by ring

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

set_option maxHeartbeats 800000 in
open scoped Chebyshev in
/-- **Von Koch's bound from the proved RH: `|ψ(x) - x| ≤ C √x log² x` for `x ≥ 55`.**

The smoothed Perron integrand `f(s) = -(ζ′/ζ)(s) · 𝓜χ_ε(s) · xˢ` (`ε = x^(-1/2)`) is moved from
`Re s = 1 + 1/log x` to the rectangle `[1/4, 1 + 1/log x] × [-T, T]`, `T ∈ [x, x + 1]` a safe height
(`TauCeti.riemannZeta_safe_height`); the poles inside are `1` (residue `𝓜χ_ε(1) x`) and the zeros
`ρ` of `ζ` (all with `Re ρ = 1/2` by RH; residue `-m(ρ) 𝓜χ_ε(ρ) x^ρ`). The residue sum is at most
`C √x ∑ m(ρ)/|ρ| ≪ √x log² x` (`sum_order_div_norm_le`); the tails give `√x log² x`, the left edge
`x^(1/4) log² x` (`logDeriv_bound_of_RH_dist` at distance `1/4`), the horizontal edges
`log² x / √x`; the sharp/smooth comparison `√x log x` and the main-term correction `√x`. -/
theorem psi_sub_le_sqrt_log_sq : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 55 ≤ x → |ψ x - x| ≤ C * √x * Real.log x ^ 2 := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := logDeriv_bound_of_RH_dist
  obtain ⟨Cs, hCs⟩ := TauCeti.riemannZeta_safe_height
  obtain ⟨Cz, hCz0, hCz⟩ := sum_order_div_norm_le
  -- the bump and the uniform Mellin bound on the strip `1/4 ≤ Re s ≤ 2`
  obtain ⟨ν, hνd, hν0, hνs, hνm, -⟩ := TauCeti.exists_smooth_symmetric_bump one_lt_two
  have hνs' : Function.support ν ∩ Set.Ioi 0 ⊆ Set.Icc (1 / 2) 2 := fun y hy ↦ by
    simpa only [one_div] using hνs hy.1
  have hν0' : ∀ y > 0, 0 ≤ ν y := fun y _ ↦ hν0 y
  have hν1 : ContDiffOn ℝ 1 ν (Set.Ioi 0) := (hνd.of_le (by exact_mod_cast le_top)).contDiffOn
  have hνi := TauCeti.integrableOn_div_of_continuousOn_of_support_subset
    (hν1.continuousOn.mono TauCeti.Icc_one_half_two_subset_Ioi) hνs'
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_mellin_smoothCutoff_le (k := 1) hν1 hνs'
    (σ₁ := 1 / 4) (σ₂ := 2) (by norm_num)
  simp only [pow_one] at hC
  have hC0 : 0 ≤ C := by
    have h := hC 1 one_pos le_rfl 1 (by norm_num) (by norm_num)
    rw [norm_one, one_mul, mul_one] at h
    exact (div_nonneg_iff.1 ((norm_nonneg _).trans h)).elim (·.1) fun h' ↦ absurd h'.2 (by norm_num)
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
  refine ⟨16 * Real.exp 1 * C + (64 * C₁ + 11) * C + 8 * Real.exp 1 * |Cs| * C + 4 * C * Cz + 11,
    by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 hx1
  have hs0 : 0 < √x := by linarith
  have hxs : x = (√x) ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hε : 0 < (√x)⁻¹ := by positivity
  have hε1 : (√x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  set L := Real.log x with hLdef
  have hL4 : 4 ≤ L := four_le_log_of_le x hx
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
  have hid := tsum_mul_smoothCutoff_eq_contour_add_sum_residue
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
      filter_upwards [riemannZeta_eventually_ne_zero hζ,
        (eventually_ne_nhds hρ1).filter_mono nhdsWithin_le_nhds] with z hz hz1
      show (G z + 1 / (z - 1)) * M z * (x : ℂ) ^ z = _
      rw [hGeq z hz1 hz, logDeriv_apply]
      ring
    rw [residue_neg_logDeriv_riemannZeta_mul hζ hH hF, norm_mul, norm_neg, Complex.norm_natCast,
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
    have h := norm_mul_mul_cpow_le' (s := (σ₀ : ℂ) + t * I) hx0.le (hLb t ht)
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
      riemannZeta_ne_zero_of_re_ne_half (by rw [hre]; norm_num) (by rw [hre]; norm_num)
    have hG : ‖G s + 1 / (s - 1)‖ ≤ 4 * C₁ * Real.log (T + 2) + 4 / 3 := by
      rw [show G s + 1 / (s - 1) = -(deriv riemannZeta s / riemannZeta s) by
        rw [hGeq s hs1 hζ]; ring, norm_neg]
      have h1 := hC₁ (1 / 4) (by norm_num) (by norm_num) s hs1 (by rw [hre]; norm_num)
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
    have h := norm_mul_mul_cpow_le' (s := s) hx0.le hG
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
    have h := norm_mul_mul_cpow_le' (s := s) hx0.le hG
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
/-- **`ψ(x) = x + O(√x log² x)` (von Koch), from the proved RH.** -/
theorem psi_sub_le_sqrt_log_sq_of_RH :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |ψ x - x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨C, -, hC⟩ := psi_sub_le_sqrt_log_sq
  exact ⟨C, 55, fun x hx ↦ hC x hx⟩

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ K √x log² x` for `x ≥ 55`. -/
theorem theta_sub_le_sqrt_log_sq : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 55 ≤ x → |θ x - x| ≤ K * √x * Real.log x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_le_sqrt_log_sq
  refine ⟨C + 6, by positivity, fun x hx ↦ ?_⟩
  have hL4 := four_le_log_of_le x hx
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hL2 : Real.log x ≤ Real.log x ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) := theta_sub_le_psi_sub_add x (by linarith)
    _ ≤ C * √x * Real.log x ^ 2 + 6 * (√x * Real.log x ^ 2) := by
        gcongr
        exact hC x hx
    _ = (C + 6) * √x * Real.log x ^ 2 := by ring

open scoped Chebyshev in
/-- **`θ(x) = x + O(√x log² x)`, from the proved RH.** -/
theorem theta_sub_le_sqrt_log_sq_of_RH :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |θ x - x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨K, -, hK⟩ := theta_sub_le_sqrt_log_sq
  exact ⟨K, 55, fun x hx ↦ hK x hx⟩

/-! ## The sharpest classical form for `π` and for the walls: `√x log x` -/

open scoped Chebyshev in
/-- `|π(⌊x⌋) - Li(x)| ≤ C √x log x` for `x ≥ 55`: Tau Ceti's `θ → π` transfer with
`ε(t) = K t^(-1/2) log² t`; the boundary term `x ε(x) / log x = K √x log x` and the integral
`∫ ε / log² = K ∫ t^(-1/2) ≤ 2 K √x` lose no logarithm. -/
theorem primeCounting_sub_logIntegral_le_sqrt_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 55 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * √x * Real.log x := by
  obtain ⟨K, hK0, hK⟩ := theta_sub_le_sqrt_log_sq
  set D1 := |(Nat.primeCounting ⌊(55 : ℝ)⌋₊ : ℝ) - TauCeti.Real.logIntegral 55|
  set ε : ℝ → ℝ := fun t ↦ K * t ^ (-(1 / 2) : ℝ) * Real.log t ^ 2
  set D3 := 55 * ε 55 / Real.log 55
  have hl55 : 4 ≤ Real.log 55 := four_le_log_of_le 55 le_rfl
  have hD3 : 0 ≤ D3 := by simp only [D3, ε]; positivity
  have hD1 : 0 ≤ D1 := abs_nonneg _
  refine ⟨D1 + D3 + K + 2 * K, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hL4 := four_le_log_of_le x hx
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
    · have : 4 ≤ Real.log t := four_le_log_of_le t ht.1
      positivity
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ K * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 55 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have h4 : ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2 ≤ 2 * K * (√x * Real.log x) := by
    calc ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2
        ≤ ∫ t in (55 : ℝ)..x, K * t ^ (-(1 / 2) : ℝ) :=
          intervalIntegral.integral_mono_on hx hcont.intervalIntegrable hint2 fun t ht ↦ by
            have hlt : 4 ≤ Real.log t := four_le_log_of_le t ht.1
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
  change _ ≤ D1 + _ + D3 + _ at hmain
  nlinarith [mul_le_mul_of_nonneg_left hsL hD1, mul_le_mul_of_nonneg_left hsL hD3]

/-- **`π(⌊x⌋) = Li(x) + O(√x log x)`, from the proved RH** (von Koch's form for `π`). -/
theorem primeCounting_sub_logIntegral_le_sqrt_log_of_RH : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * √x * Real.log x := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_sqrt_log
  exact ⟨C, 55, fun x hx ↦ hC x hx⟩

open Classical in
/-- **The walls meet RH at `√N log N`.** There are `C` and `N₀` such that for every `N ≥ N₀`
the wall count `2 + #{n ≤ N that pass the wall test}` differs from `Li(N)` by at most
`C √N log N`. From `riemannHypothesis` (through `primeCounting_sub_logIntegral_le_sqrt_log`)
and Rayn-McLean's `prime_count_walls`. -/
theorem walls_meet_rh_sqrt_log : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((2 + ((Finset.range (N + 1)).filter passes).card : ℕ) : ℝ) -
      TauCeti.Real.logIntegral N| ≤ C * √(N : ℝ) * Real.log (N : ℝ) := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_sqrt_log
  refine ⟨C, 55, fun N hN ↦ ?_⟩
  have h := hC N (by exact_mod_cast hN)
  rwa [Nat.floor_natCast, prime_count_walls N (by omega)] at h

end WallsMeetRHVonKoch

#print axioms riemannHypothesis
#print axioms WallsMeetRHVonKoch.prime_count_walls
#print axioms WallsMeetRHVonKoch.logDeriv_bound_of_RH_dist
#print axioms WallsMeetRHVonKoch.sum_order_div_norm_le
#print axioms WallsMeetRHVonKoch.residue_neg_logDeriv_riemannZeta_mul
#print axioms WallsMeetRHVonKoch.tsum_mul_smoothCutoff_eq_contour_add_sum_residue
#print axioms WallsMeetRHVonKoch.psi_sub_le_sqrt_log_sq
#print axioms WallsMeetRHVonKoch.psi_sub_le_sqrt_log_sq_of_RH
#print axioms WallsMeetRHVonKoch.theta_sub_le_sqrt_log_sq_of_RH
#print axioms WallsMeetRHVonKoch.primeCounting_sub_logIntegral_le_sqrt_log_of_RH
#print axioms WallsMeetRHVonKoch.walls_meet_rh_sqrt_log

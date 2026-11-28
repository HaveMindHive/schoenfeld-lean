/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Schoenfeld's theta bound on the closed real interval [599, 1024] -/

namespace SchoenfeldThetaInterval

open Real

-- Use the least prime factor to keep kernel reduction of each endpoint small.
private def primeProduct : ℕ → ℕ
  | 0 => 1
  | n + 1 => primeProduct n * (if 2 ≤ n + 1 ∧ (n + 1).minFac = n + 1 then n + 1 else 1)

private theorem primeProduct_eq (n : ℕ) : primeProduct n = primorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [primeProduct, ih]
    simp only [primorial, Finset.prod_filter, Finset.prod_range_succ _ (n+1), Nat.prime_def_minFac]

private theorem lower (n k : ℕ) (h : 2 ^ k ≤ primorial n) :
    k * log 2 ≤ Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, ← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h

private theorem upper (n k : ℕ) (h : primorial n ≤ 2 ^ k) :
    Chebyshev.theta n ≤ k * log 2 := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, ← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast primorial_pos n)
  exact_mod_cast h

private theorem budget {x : ℝ} (hx : 599 ≤ x) :
    38.5 < √x * log x ^ 2 / (8 * π) := by
  have hs : (24 : ℝ) ≤ √x := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hpow : (2 : ℝ) ^ 46 ≤ x ^ 5 :=
    le_trans (by norm_num : (2 : ℝ) ^ 46 ≤ 599 ^ 5) (pow_le_pow_left₀ (by norm_num) hx 5)
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num1 at hl
  have hlog : (6.37 : ℝ) ≤ log x := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul hs (pow_le_pow_left₀ (by norm_num) hlog 2) (by norm_num) (by positivity)
  apply (lt_div_iff₀ (by positivity)).2
  linarith [Real.pi_lt_d2]

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 1024 in
/-- The strict theta estimate holds at both endpoints and every real point between. -/
theorem theta_599_613 {x : ℝ} (hx : 599 ≤ x) (hy : x ≤ 613) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  have hi := (Chebyshev.theta_mono hy).trans
    (upper 613 850 (by rw [← primeProduct_eq]; decide +kernel))
  norm_num1 at hi
  have hu : Chebyshev.theta x - x < 38.5 := by linarith [Real.log_two_lt_d9]
  have hd : x - Chebyshev.theta x < 38.5 := by
    by_cases h₁ : x ≤ 601
    · have h := (lower 599 812 (by rw [← primeProduct_eq]; decide +kernel)).trans
        (Chebyshev.theta_mono hx)
      norm_num1 at h
      linarith [Real.log_two_gt_d9]
    by_cases h₂ : x ≤ 607
    · have h := (lower 601 821 (by rw [← primeProduct_eq]; decide +kernel)).trans
        (Chebyshev.theta_mono (le_of_not_ge h₁))
      norm_num1 at h
      linarith [Real.log_two_gt_d9]
    · have h := (lower 607 830 (by rw [← primeProduct_eq]; decide +kernel)).trans
        (Chebyshev.theta_mono (le_of_not_ge h₂))
      norm_num1 at h
      linarith [Real.log_two_gt_d9]
  exact (abs_lt.mpr ⟨by linarith, hu⟩).trans (budget hx)

-- At a left endpoint a, s / 10 bounds its square root and e * 0.693 / 64 bounds its log.
private def allowance (s e : ℕ) : ℚ :=
  (s / 10 : ℚ) * ((e : ℚ) * (693 / 1000) / 64) ^ 2 / (8 * (315 / 100))

private theorem allowance_le {a : ℕ} {x : ℝ} (ha : 0 < a) (hx : (a : ℝ) ≤ x) :
    (allowance (100 * a).sqrt (a ^ 64).log2 : ℝ) ≤ √x * log x ^ 2 / (8 * π) := by
  let s := (100 * a).sqrt
  let e := (a ^ 64).log2
  have hs0 : (s : ℝ) * s ≤ 100 * (a : ℝ) := by exact_mod_cast Nat.sqrt_le (100 * a)
  have hs : (s : ℝ) / 10 ≤ √x :=
    (Real.le_sqrt (by positivity) ((Nat.cast_nonneg a).trans hx)).2
      (by nlinarith)
  have hpow : (2 : ℝ) ^ e ≤ (a : ℝ) ^ 64 := by
    exact_mod_cast Nat.log2_self_le (pow_ne_zero 64 ha.ne')
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num1 at hl
  have hex : (e : ℝ) * (693 / 1000) / 64 ≤ log x := by
    have hc := mul_le_mul_of_nonneg_left
      (by linarith [Real.log_two_gt_d9] : (693 / 1000 : ℝ) ≤ log 2)
      (Nat.cast_nonneg e (α := ℝ))
    have hm := Real.log_le_log (Nat.cast_pos.mpr ha) hx
    linarith
  have hm := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hex 2) (by positivity) (by positivity)
  change ((allowance s e : ℚ) : ℝ) ≤ _
  simp only [allowance, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat]
  exact div_le_div₀ (by positivity) hm (by positivity) (by linarith [Real.pi_lt_d2])

private def tileOK (a b : ℕ) : Bool :=
  let cap := allowance (100 * a).sqrt (a ^ 64).log2
  let lo := (primeProduct a).log2
  let hi := (primeProduct b).log2 + 1
  decide (0 < a ∧ (b : ℚ) - lo * (693 / 1000) < cap ∧ hi * (694 / 1000) - (a : ℚ) < cap)

private theorem tile_sound {a b : ℕ} {x : ℝ} (ok : tileOK a b = true)
    (hx : (a : ℝ) ≤ x) (hy : x ≤ b) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  simp only [tileOK, decide_eq_true_eq, primeProduct_eq] at ok
  obtain ⟨ha, hlo, hhi⟩ := ok
  let lo := (primorial a).log2
  let hi := (primorial b).log2 + 1
  let cap := allowance (100 * a).sqrt (a ^ 64).log2
  have hl : (b : ℝ) - lo * (693 / 1000) < (cap : ℝ) := by
    change (b : ℚ) - (lo : ℚ) * (693 / 1000) < cap at hlo
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
      using (Rat.cast_lt (K := ℝ)).2 hlo
  have hr : hi * (694 / 1000) - (a : ℝ) < (cap : ℝ) := by
    change (hi : ℚ) * (694 / 1000) - (a : ℚ) < cap at hhi
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
      using (Rat.cast_lt (K := ℝ)).2 hhi
  have h₁ := (lower a lo (Nat.log2_self_le (primorial_pos a).ne')).trans (Chebyshev.theta_mono hx)
  have h₂ := (Chebyshev.theta_mono hy).trans (upper b hi Nat.lt_log2_self.le)
  have hd := mul_le_mul_of_nonneg_left
    (by linarith [Real.log_two_gt_d9] : (693 / 1000 : ℝ) ≤ log 2)
    (Nat.cast_nonneg lo (α := ℝ))
  have hu := mul_le_mul_of_nonneg_left
    (by linarith [Real.log_two_lt_d9] : log 2 ≤ (694 / 1000 : ℝ))
    (Nat.cast_nonneg hi (α := ℝ))
  exact lt_of_lt_of_le (abs_lt.mpr ⟨by linarith, by linarith⟩ : |Chebyshev.theta x - x| < cap)
    (allowance_le ha hx)

private def cover (a last : ℕ) : List ℕ → Bool
  | [] => false
  | b :: bs => tileOK a b && (decide (last ≤ b) || cover b last bs)

private theorem cover_sound {a last : ℕ} {x : ℝ} (bs : List ℕ) (ok : cover a last bs = true)
    (hx : (a : ℝ) ≤ x) (hy : x ≤ last) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  induction bs generalizing a with
  | nil => contradiction
  | cons b bs ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp ok
    by_cases h : x ≤ (b : ℝ)
    · exact tile_sound head hx h
    · rcases Bool.or_eq_true_iff.mp tail with done | rest
      · have hlast : last ≤ b := of_decide_eq_true done
        exact (h (hy.trans (by exact_mod_cast hlast))).elim
      · exact ih rest (le_of_lt (lt_of_not_ge h))

set_option maxRecDepth 8192 in
/-- The next closed interval, certified by a list of right endpoints. -/
theorem theta_613_1024 {x : ℝ} (hx : 613 ≤ x) (hy : x ≤ 1024) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  let endpoints : List ℕ := [621, 635, 642, 649, 662, 682, 696, 710, 724, 731, 738, 745,
      759, 773, 793, 801, 808, 809, 815, 822, 829, 850, 857, 871, 885, 907, 921, 936,
      943, 957, 971, 986, 1000, 1015, 1024]
  exact cover_sound (a := 613) (last := 1024) endpoints (by decide +kernel)
      (by simpa using hx) (by simpa using hy)

/-- Schoenfeld's strict bound on the combined closed real interval [599, 1024]. -/
theorem theta_599_1024 {x : ℝ} (hx : 599 ≤ x) (hy : x ≤ 1024) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  by_cases h : x ≤ 613
  · exact theta_599_613 hx h
  · exact theta_613_1024 (le_of_lt (lt_of_not_ge h)) hy

end SchoenfeldThetaInterval

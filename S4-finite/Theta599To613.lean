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

/-! # Schoenfeld's theta bound on the closed real interval [599, 613] -/

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

end SchoenfeldThetaInterval

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Factorial

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1515Z-cloud27, unit U-5650.

# Chebyshev's explicit lower bound with the weight 1, -1/2, -1/3, -1/5, +1/30

`psi_ge_chebyshev30`: for every natural `n ≥ 30`,
`ψ(n) ≥ A n - 5 log n + 2 log 30 - 1` with `A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30`,
`A = 0.92129...`. `pi_ge_chebyshev30`: `π(n) ≥ (0.9212 n - 5 log n) / log n` for `n ≥ 30`.

Mathlib's `Chebyshev.psi_ge` and `Chebyshev.pi_ge` have the constant `log 2 = 0.6931`.

Proof, Chebyshev 1852. Put `C(n) = log n! - log ⌊n/2⌋! - log ⌊n/3⌋! - log ⌊n/5⌋! + log ⌊n/30⌋!`.
By Legendre, `C(n) = Σ_{p ≤ n} log p Σ_{i ≥ 1} S(⌊n/p^i⌋)` with
`S(k) = k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋ ≤ 1`, so `C(n) ≤ Σ_p ⌊log_p n⌋ log p = ψ(n)`.
Mathlib's two-sided bound `x log x - x - log x + 1 ≤ log ⌊x⌋! ≤ x log x - x + log x + 1` then gives
`C(n) ≥ A n - 5 log n + 2 log 30 - 1`.

KNOWN mathematics, Chebyshev 1852. No cited input. Goldbach is open.
-/

open Real Finset Chebyshev

noncomputable section
namespace SchoenfeldPort.ChebyshevExplicit

/-- Legendre over any prime range containing `m`: `log m! = Σ_{p ≤ n} v_p(m!) log p`. -/
lemma log_factorial_eq_of_le {m n : ℕ} (hmn : m ≤ n) :
    Real.log ((m.factorial : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((m.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle : p ≤ m := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, hle.trans hmn⟩, hpp⟩
  · intro p _; simp

/-- `log ⌊n/j⌋! = log ⌊(n : ℝ)/j⌋₊!` written as Mathlib's partial sum of `log`. -/
lemma log_fact_div (n j : ℕ) :
    Real.log ((n / j).factorial : ℝ) = ∑ k ∈ Ioc 0 ⌊(n : ℝ) / j⌋₊, Real.log k := by
  rw [Nat.floor_div_eq_div, Real.sum_log_eq_log_factorial]

/-- The constant `A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30`. -/
def A : ℝ := Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

/-- `p^b ≥ 2^a` gives `log p ≥ (a/b) log 2`. -/
lemma log_ge_of_pow (p a b : ℕ) (h : 2 ^ a ≤ p ^ b) (hb : 0 < b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log p := by
  have h' : ((2 : ℝ)) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast h
  have hp : (0 : ℝ) < (p : ℝ) ^ b := lt_of_lt_of_le (by positivity) h'
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']; linarith

/-- Numerical value: `A > 0.9212`. -/
lemma A_gt : (0.9212 : ℝ) < A := by
  have h2 := Real.log_two_gt_d9
  have h3 := log_ge_of_pow 3 84 53 (by norm_num) (by norm_num)
  have h5 := log_ge_of_pow 5 65 28 (by norm_num) (by norm_num)
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  push_cast at h3 h5
  unfold A; rw [h30]; linarith

end SchoenfeldPort.ChebyshevExplicit



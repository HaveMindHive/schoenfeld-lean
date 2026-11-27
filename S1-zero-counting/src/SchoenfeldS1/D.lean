/-
Schoenfeld S1, part D (groundwork): the two ingredients of Backlund's disc argument for `S(T)`.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the ported
goldbach-lean modules (SchoenfeldPort, Steve Hubbard, Apache-2.0), Mathlib 31ce06ea and Tau Ceti,
in the environment of the riemann-hypothesis-community repository (Lean v4.37.0-rc1). Apache-2.0.
-/
import SchoenfeldPort.Final

/-!
# Backlund's disc: explicit size of `ζ` and the value at the centre

Backlund bounds `S(T)` by Jensen's formula for `g(s) = (ζ(s + iT) + ζ(s - iT))/2 = Re ζ` on the
real segment, on a disc about `2 + iT`. The two inputs are an explicit upper bound for `|ζ|` on the
disc and a lower bound for `|g|` at the centre.

* `norm_riemannZeta_le_on_disc`: for `T ≥ 3` and `‖s - (2 + iT)‖ ≤ 7/4`, `‖ζ s‖ ≤ 4T + 24`
  (from the port's `norm_zeta_le : ‖ζ s‖ ≤ 2 + ‖s‖/Re s`, crude but explicit).
* `re_riemannZeta_two_add_ge`: `Re ζ(2 + iT) ≥ 2 - π²/6` (`= 0.355...`), from
  `Re Σ n^{-2-iT} ≥ 1 - Σ_{n ≥ 2} n^{-2}`.
-/

namespace SchoenfeldS1

open Complex Real

local notation "ζ" => riemannZeta

/-- On the disc of radius `7/4` about `2 + iT`, `T ≥ 3`: `‖ζ s‖ ≤ 4T + 24`. -/
theorem norm_riemannZeta_le_on_disc {T : ℝ} (hT : 3 ≤ T) {s : ℂ}
    (hs : ‖s - (2 + T * I)‖ ≤ 7 / 4) : ‖ζ s‖ ≤ 4 * T + 24 := by
  have hre : |(s - (2 + T * I)).re| ≤ 7 / 4 := (Complex.abs_re_le_norm _).trans hs
  have him : |(s - (2 + T * I)).im| ≤ 7 / 4 := (Complex.abs_im_le_norm _).trans hs
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at hre him
  norm_num at hre him
  rw [abs_le] at hre him
  have hsre : 1 / 4 ≤ s.re := by linarith [hre.1]
  have hsim : T - 7 / 4 ≤ s.im := by linarith [him.1]
  -- `‖s - 1‖ ≥ |Im s| ≥ T - 7/4 ≥ 1`
  have h1 : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have e : (s - 1).im = s.im := by simp
    rw [e] at this
    linarith [le_abs_self s.im]
  have hb := SchoenfeldPort.PNTPort.ZetaZeros.norm_zeta_le (by linarith : 0 < s.re) h1
  -- `‖s‖ ≤ |Re s| + |Im s| ≤ (2 + 7/4) + (T + 7/4)`
  have hn : ‖s‖ ≤ T + 11 / 2 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have a : |s.re| ≤ 15 / 4 := by rw [abs_le]; constructor <;> linarith [hre.1, hre.2]
    have b : |s.im| ≤ T + 7 / 4 := by rw [abs_le]; constructor <;> linarith [him.1, him.2]
    linarith
  have hdiv : ‖s‖ / s.re ≤ (T + 11 / 2) / (1 / 4) := by
    apply div_le_div₀ (by linarith) hn (by norm_num) hsre
  have : (T + 11 / 2) / (1 / 4) = 4 * T + 22 := by ring
  linarith

/-- `Re ζ(2 + iT) ≥ 2 - π²/6`. -/
theorem re_riemannZeta_two_add_ge (T : ℝ) : 2 - π ^ 2 / 6 ≤ (ζ (2 + T * I)).re := by
  have hs : 1 < (2 + T * I : ℂ).re := by simp
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  -- summability of the terms and of their real parts
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (2 + T * I)) := by
    simpa using (summable_one_div_nat_cpow (p := (2 + T * I : ℂ)).mpr hs)
  rw [Complex.re_tsum hsum]
  -- termwise: `Re (1/n^{2+iT}) ≥ -1/n²` for `n ≥ 2`, `= 1` at `n = 1`, `= 0` at `n = 0`
  have hterm : ∀ n : ℕ, (1 / (n : ℂ) ^ (2 + T * I)).re ≥
      (if n = 1 then (1 : ℝ) else 0) - (if 2 ≤ n then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hexp : (2 + T * I : ℂ) ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this
      interval_cases n
      · simp [Complex.zero_cpow hexp]
      · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hnorm : ‖1 / (n : ℂ) ^ (2 + T * I)‖ = 1 / (n : ℝ) ^ 2 := by
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega)]
        simp
      have := neg_abs_le (1 / (n : ℂ) ^ (2 + T * I)).re
      have h2 := Complex.abs_re_le_norm (1 / (n : ℂ) ^ (2 + T * I))
      rw [hnorm] at h2
      have hne : n ≠ 1 := by omega
      simp only [hne, ite_false, hn, ite_true]
      linarith
  have hre_sum : Summable (fun n : ℕ => (1 / (n : ℂ) ^ (2 + T * I)).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hA : Summable (fun n : ℕ => (if n = 1 then (1 : ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := {1}) (fun n hn => by simp at hn; simp [hn])
  have hB : Summable (fun n : ℕ => (if 2 ≤ n then 1 / (n : ℝ) ^ 2 else 0)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    split_ifs <;> [exact le_rfl; positivity]
  have hle := Summable.tsum_le_tsum (fun n => hterm n) (hA.sub hB) hre_sum
  rw [Summable.tsum_sub hA hB] at hle
  have hA' : ∑' n : ℕ, (if n = 1 then (1 : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 1 (fun n hn => by simp [hn])]; simp
  have hB' : ∑' n : ℕ, (if 2 ≤ n then 1 / (n : ℝ) ^ 2 else 0) = π ^ 2 / 6 - 1 := by
    have h := hasSum_zeta_two
    -- split off `n = 0` (term `0`) and `n = 1` (term `1`)
    have hsplit : (fun n : ℕ => (if 2 ≤ n then 1 / (n : ℝ) ^ 2 else 0)) =
        fun n : ℕ => 1 / (n : ℝ) ^ 2 - (if n = 1 then (1 : ℝ) else 0) := by
      funext n
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n <;> simp
      · have : n ≠ 1 := by omega
        simp [hn, this]
    rw [hsplit, Summable.tsum_sub h.summable hA, h.tsum_eq, hA']
  rw [hA', hB'] at hle
  linarith

end SchoenfeldS1

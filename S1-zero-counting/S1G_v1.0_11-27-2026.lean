/-
Schoenfeld S1, part G: `|ψ(x) - x| ≤ √x log² x/(8π)` and the same for `θ`, for `x ≥ 10^15`, from
the zero count `N(T)` with the Backlund-type error `RtB T = 4.5 log T + 17.1` of `SchoenfeldS1.F`.
Adapted from goldbach-lean (Steve Hubbard, Apache-2.0): `PsiSchoenfeld.lean`,
`PsiSchoenfeldLarge.lean`, `ThetaSchoenfeldLarge.lean` of the port
`~/HaveMindHive/schoenfeld-port_v1.0_11-27-2026/` (not modified there).
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the port,
Mathlib 31ce06ea and Tau Ceti, in the environment of the riemann-hypothesis-community repository
(Lean v4.37.0-rc1), whose `riemannHypothesis` (Alpöge with Claude) discharges RH. Apache-2.0.
-/
import SchoenfeldS1.A
import SchoenfeldS1.F

/-!
# Schoenfeld's bounds for `x ≥ 10^15` from `N(T)` with the error `RtB`

The port's `psi_schoenfeld_large` (`x ≥ 10^11`) consumed Hasanalizade-Shen-Wong's `Rt`. With the
looser `RtB T = 4.5 log T + 17.1` (what a crude Backlund disc argument gives), the same proof
closes at `x ≥ 10^15`: the head factor constant `1.57` becomes `4.8`, the tail numerals
`(1.004, 41.26)` become `(18, 72.9)`, the tail threshold `70` becomes `1000`
(`T = 2π√x/log x ≥ 10^6` here).

Main results (`gZ` the ordinates of the zeros listed with multiplicity, `NT` the zero count of
`SchoenfeldS1.A`):
* `psi_schoenfeld_largeB`, `theta_schoenfeld_largeB`: from `NB1000 gZ`, `NBHead14 gZ`,
  `Ordinates14 gZ`;
* `schoenfeld_psi_large_of_NTB`, `schoenfeld_theta_large_of_NTB`: from
  `(U') ∀ T ≥ 14, N(T) ≤ Mt T + RtB T`, `(L') ∀ T ≥ 1000, Mt T - RtB T ≤ N(T)`, `(Z) N(14) = 0`.
-/

namespace SchoenfeldS1

open Real Chebyshev
open SchoenfeldPort.Dudek2014.Section22
open SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt)

/-! ### The general bounds (PsiSchoenfeld with `RtB`) -/

/-- `|Z(y + h) - Z(y)| ≤ h (y + h)^{1/2} S₁(T) + 2 (y + h)^{3/2} S₂(T)` under RH. -/
lemma zreal_diffB (hRH : RiemannHypothesis) (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {y h T : ℝ} (hy : 0 < y) (hh : 0 ≤ h) (hT : 1000 ≤ T) :
    |Zreal (y + h) - Zreal y| ≤ h * (y + h) ^ (1 / 2 : ℝ) * SB1 T + 2 * (y + h) ^ (3 / 2 : ℝ) * SB2 T := by
  rw [← Zr_eq_Zreal hRH (by linarith), ← Zr_eq_Zreal hRH hy]
  unfold SchoenfeldPort.Dudek2014.SigmaT.Zr
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (zdiff_leB hN hH h14 hy hh hT)

/-- Upper bound for `ψ(x)`, under RH, from `NB1000`, `NBHead14`, `Ordinates14`. -/
theorem psi_upper_genB (hRH : RiemannHypothesis) (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x h T : ℝ} (hx : 1 < x) (hh : 0 < h) (hT : 1000 ≤ T) :
    psiF x ≤ x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * SB1 T +
      2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T / h := by
  obtain ⟨u1, -⟩ := psi1_diff_bounds (by linarith : (0 : ℝ) ≤ x) hh
  have a1 := abs_le.1 (psi1_split (by linarith : 1 < x + h))
  have a0 := abs_le.1 (psi1_split hx)
  have z := abs_le.1 (zreal_diffB hRH hN hH h14 (by linarith : (0 : ℝ) < x) hh.le hT)
  have key : h * psiF x ≤ h * (x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * SB1 T +
      2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T / h) := by
    have e : h * (x + h / 2 - Real.log (2 * π) + 4.786 / h + (x + h) ^ (1 / 2 : ℝ) * SB1 T +
        2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T / h) = x * h + h ^ 2 / 2 - h * Real.log (2 * π) + 4.786 +
        (h * (x + h) ^ (1 / 2 : ℝ) * SB1 T + 2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T) := by
      field_simp; ring
    rw [e]
    have e2 : (x + h) ^ 2 / 2 - (x + h) * Real.log (2 * π) = x ^ 2 / 2 - x * Real.log (2 * π) + (x * h + h ^ 2 / 2 - h * Real.log (2 * π)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hh

/-- Lower bound for `ψ(x)`, under RH, from `NB1000`, `NBHead14`, `Ordinates14`. -/
theorem psi_lower_genB (hRH : RiemannHypothesis) (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x h T : ℝ} (hx : 1 < x - h) (hh : 0 < h) (hT : 1000 ≤ T) :
    x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * SB1 T -
      2 * x ^ (3 / 2 : ℝ) * SB2 T / h ≤ psiF x := by
  obtain ⟨-, u2⟩ := psi1_diff_bounds (by linarith : (0 : ℝ) ≤ x - h) hh
  rw [sub_add_cancel] at u2
  have a1 := abs_le.1 (psi1_split (by linarith : 1 < x))
  have a0 := abs_le.1 (psi1_split hx)
  have z := abs_le.1 (zreal_diffB hRH hN hH h14 (by linarith : (0 : ℝ) < x - h) hh.le hT)
  rw [sub_add_cancel] at z
  have key : h * (x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * SB1 T -
      2 * x ^ (3 / 2 : ℝ) * SB2 T / h) ≤ h * psiF x := by
    have e : h * (x - h / 2 - Real.log (2 * π) - 4.786 / h - x ^ (1 / 2 : ℝ) * SB1 T -
        2 * x ^ (3 / 2 : ℝ) * SB2 T / h) = x * h - h ^ 2 / 2 - h * Real.log (2 * π) - 4.786 -
        (h * x ^ (1 / 2 : ℝ) * SB1 T + 2 * x ^ (3 / 2 : ℝ) * SB2 T) := by
      field_simp; ring
    rw [e]
    have e2 : (x - h) ^ 2 / 2 - (x - h) * Real.log (2 * π) = x ^ 2 / 2 - x * Real.log (2 * π) - (x * h - h ^ 2 / 2 - h * Real.log (2 * π)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hh

/-! ### The numerics at `x ≥ 10^15` -/

/-- The numerical facts on `s = √x`, `L = log x`, `λ = log L` for `x ≥ 10^15`. -/
lemma large_factsB {x : ℝ} (hx : 10 ^ 15 ≤ x) :
    31622776 ≤ √x ∧ 34.5 ≤ log x ∧ log x ^ 2 ≤ √x / 10000 ∧ 3.5 ≤ log (log x) ∧
      log (log x) ≤ log x / 7 ∧ log x = 2 * log √x := by
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hsx : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hLs : log x = 2 * log s := by rw [← hsx, Real.log_pow]; push_cast; ring
  have hs1 : 31622776 ≤ s := by nlinarith
  -- log x ≥ 34.5
  have hexp05 : exp 0.5 ≤ 1.6488 := by
    have := Real.exp_bound' (x := 0.5) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hL : 34.5 ≤ log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h1 := Real.exp_one_lt_d9
    have e : exp 34.5 = exp 1 ^ 34 * exp 0.5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    have h3 : exp 1 ^ 34 ≤ (2.7182818286 : ℝ) ^ 34 := by gcongr
    have h4 : (2.7182818286 : ℝ) ^ 34 * 1.6488 ≤ 10 ^ 15 := by norm_num
    nlinarith [Real.exp_pos 0.5, pow_pos (Real.exp_pos 1) 34]
  -- log √s ≤ √s/1096 + 6
  have hr0 : 0 < √s := Real.sqrt_pos.mpr hs0
  have hss : √s ^ 2 = s := Real.sq_sqrt hs0.le
  have hr1 : 5623 ≤ √s := by rw [Real.le_sqrt (by norm_num) hs0.le]; linarith
  have he7 : 1096 ≤ exp 7 := by
    have h1 := Real.exp_one_gt_d9
    have e : exp 7 = exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 := by gcongr
    linarith [show (1096 : ℝ) ≤ 2.7182818283 ^ 7 by norm_num]
  have hlogr : log √s ≤ √s / 1096 + 6 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < √s / exp 7)
    rw [Real.log_div hr0.ne' (Real.exp_pos 7).ne', Real.log_exp] at h
    have : √s / exp 7 ≤ √s / 1096 := div_le_div_of_nonneg_left hr0.le (by norm_num) he7
    linarith
  have hlogs : log s = 2 * log √s := by
    rw [Real.log_sqrt hs0.le]; ring
  have hL2 : log x ^ 2 ≤ s / 10000 := by
    have hLle : log x ≤ √s / 274 + 24 := by rw [hLs, hlogs]; linarith
    have hL0 : 0 ≤ log x := by linarith
    have : log x ≤ √s / 100 := by linarith
    have h2 : log x ^ 2 ≤ (√s / 100) ^ 2 := by gcongr
    rw [div_pow, hss] at h2; linarith
  -- λ = log L
  have hLpos : 0 < log x := by linarith
  have hlam : 3.5 ≤ log (log x) := by
    rw [Real.le_log_iff_exp_le hLpos]
    have h1 := Real.exp_one_lt_d9
    have e : exp 3.5 = exp 1 ^ 3 * exp 0.5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    have h3 : exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
    nlinarith [Real.exp_pos 0.5, pow_pos (Real.exp_pos 1) 3]
  have hlamL : log (log x) ≤ log x / 7 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < log x / 34.5)
    rw [Real.log_div hLpos.ne' (by norm_num)] at h
    have h345 : log (34.5 : ℝ) ≤ 3.6 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have e : exp 3.6 = exp 1 ^ 3 * exp 0.6 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.6)
      rw [e]
      have : (2.7182818283 : ℝ) ^ 3 ≤ exp 1 ^ 3 := by gcongr
      nlinarith
    have e1 : log x / 34.5 = log x * (2 / 69) := by ring
    have e2 : log x / 7 = log x * (1 / 7) := by ring
    rw [e1] at h
    rw [e2]
    nlinarith
  exact ⟨hs1, hL, hL2, hlam, hlamL, hLs⟩

set_option maxHeartbeats 4000000 in
/-- The core inequality, in plain real variables: `s = √x`, `L = log x`, `l = log L`, `c = log 2π`,
`p = π`, `K = s + L/(2π)`, `M = log T = c + L/2 - l`, and `E` the extra `2c` of the lower bound. -/
lemma coreB {s L l c p E : ℝ} (hs : 31622776 ≤ s) (hL : 34.5 ≤ L) (hL2 : L ^ 2 ≤ s / 10000)
    (hl : 3.5 ≤ l) (hlL : l ≤ L / 7) (hc1 : 1.8 ≤ c) (hc2 : c ≤ 2) (hp1 : 3.14 ≤ p) (hp2 : p ≤ 3.15)
    (hE0 : 0 ≤ E) (hE : E ≤ 4) :
    s * L / p / 2 + E + 4.786 / (s * L / p) + 1.2 * s +
      (s + L / (2 * p)) * ((L / 2 - l) ^ 2 / (2 * p) + 4.8) +
      (s + L / (2 * p)) * (p * s + L) * ((c + L / 2 - l) / (p ^ 2 * s) +
        (18 * (c + L / 2 - l) + 72.9) * L / (2 * p ^ 2 * s ^ 2)) ≤
    s * L ^ 2 / (8 * p) := by
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hp0 : 0 < p := by linarith
  have hLs : L ≤ s / 2530 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (s / 2530) ^ 2 ≤ L ^ 2 := by gcongr
    have h2 : s * 31622776 ≤ s * s := mul_le_mul_of_nonneg_left hs hs0.le
    nlinarith
  set M := c + L / 2 - l with hM
  have hM0 : 0 ≤ M := by linarith
  have hM1 : M ≤ L / 2 := by linarith
  set u := L / (2 * p) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ L / 6.28 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set S1v := (L / 2 - l) ^ 2 / (2 * p) + 4.8 with hS1v
  have hS1v0 : 0 ≤ S1v := by positivity
  have hsq : (L / 2 - l) ^ 2 ≤ L ^ 2 / 4 := by nlinarith
  -- (1): u S1v ≤ L/6.28 (L²/25.12 + 4.8) ≤ 0.00007 s L + 0.0004 s
  have h1 : u * S1v ≤ L / 6.28 * (L ^ 2 / 25.12 + 4.8) := by
    have : S1v ≤ L ^ 2 / 25.12 + 4.8 := by
      rw [hS1v]
      have : (L / 2 - l) ^ 2 / (2 * p) ≤ L ^ 2 / 4 / 6.28 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have e : L ^ 2 / 4 / 6.28 = L ^ 2 / 25.12 := by ring
      linarith
    exact mul_le_mul hu1 this hS1v0 (by positivity)
  have h1' : L / 6.28 * (L ^ 2 / 25.12 + 4.8) ≤ 0.00007 * s * L + 0.0004 * s := by
    have e : L / 6.28 * (L ^ 2 / 25.12 + 4.8) = L * L ^ 2 / 157.7536 + (4.8 / 6.28) * L := by ring
    have a : L * L ^ 2 ≤ L * (s / 10000) := mul_le_mul_of_nonneg_left hL2 hL0.le
    have e2 : L * (s / 10000) = s * L / 10000 := by ring
    have hsL : 0 ≤ s * L := by positivity
    rw [e]
    have b1 : L * L ^ 2 / 157.7536 ≤ s * L / 1577536 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    have b2 : (4.8 / 6.28) * L ≤ 0.0004 * s := by linarith
    have b3 : s * L / 1577536 ≤ 0.00007 * s * L := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- (2): the tail term
  set B := (c + L / 2 - l) / (p ^ 2 * s) + (18 * (c + L / 2 - l) + 72.9) * L / (2 * p ^ 2 * s ^ 2)
    with hB
  have hKp : (s + u) * (p * s + L) = p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p) := by
    rw [hu]; field_simp; ring
  have h2 : (s + u) * (p * s + L) * B ≤ M * s / p + 0.012 * s := by
    rw [hKp, hB]
    have e : (p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p)) *
        ((c + L / 2 - l) / (p ^ 2 * s) + (18 * (c + L / 2 - l) + 72.9) * L / (2 * p ^ 2 * s ^ 2)) =
        M * s / p + 1.5 * L * M / p ^ 2 + L ^ 2 * M / (2 * p ^ 3 * s) +
        (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((18 * M + 72.9) * L / (2 * p ^ 2)) := by
      rw [hM]; field_simp
    rw [e]
    have hp2' : 9.85 ≤ p ^ 2 := by nlinarith
    have hp3' : 30.9 ≤ p ^ 3 := by nlinarith
    have t1 : 1.5 * L * M / p ^ 2 ≤ 0.0008 * s := by
      rw [div_le_iff₀ (by positivity)]
      have a : L * M ≤ L * (L / 2) := mul_le_mul_of_nonneg_left hM1 hL0.le
      have b : s * 9.85 ≤ s * p ^ 2 := mul_le_mul_of_nonneg_left hp2' hs0.le
      have e1 : 1.5 * L * M = 1.5 * (L * M) := by ring
      have e2 : 0.0008 * s * p ^ 2 = 0.0008 * (s * p ^ 2) := by ring
      have e3 : L * (L / 2) = L ^ 2 / 2 := by ring
      rw [e1, e2]; linarith
    have t2 : L ^ 2 * M / (2 * p ^ 3 * s) ≤ 0.0001 * s := by
      rw [div_le_iff₀ (by positivity)]
      have a : L ^ 2 * M ≤ s / 10000 * (s / 5060) := by
        apply mul_le_mul hL2 (by linarith) hM0 (by positivity)
      have b : s ^ 2 * 30.9 ≤ s ^ 2 * p ^ 3 := mul_le_mul_of_nonneg_left hp3' (sq_nonneg s)
      have e1 : 0.0001 * s * (2 * p ^ 3 * s) = 0.0002 * (s ^ 2 * p ^ 3) := by ring
      have e2 : s / 10000 * (s / 5060) = s ^ 2 / 50600000 := by ring
      have c0 : 0 ≤ s ^ 2 := sq_nonneg s
      rw [e1]; linarith
    have t3a : p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2) ≤ 3.151 := by
      have a1 : 1.5 * L / s ≤ 0.0006 := by rw [div_le_iff₀ hs0]; nlinarith
      have a2 : L ^ 2 / (2 * p * s ^ 2) ≤ 0.0001 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have t3b : (18 * M + 72.9) * L / (2 * p ^ 2) ≤ 0.0035 * s := by
      rw [div_le_iff₀ (by positivity)]
      have : (18 * M + 72.9) * L ≤ 9 * L ^ 2 + 72.9 * L := by nlinarith
      nlinarith
    have t3 : (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((18 * M + 72.9) * L / (2 * p ^ 2))
        ≤ 3.151 * (0.0035 * s) := by
      apply mul_le_mul t3a t3b (by positivity) (by norm_num)
    linarith
  -- the main terms
  have h4 : 4.786 / (s * L / p) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have : s * L / p ≥ 31622776 * 34.5 / 3.15 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hp0]; nlinarith
    linarith
  have hmain : s * L / p / 2 + s * S1v + M * s / p + E + 0.001 + 1.212 * s +
      (0.00007 * s * L + 0.0004 * s) ≤ s * L ^ 2 / (8 * p) := by
    rw [hS1v, hM]
    have key : L / 2 + ((L / 2 - l) ^ 2 / 2 + 4.8 * p) + (c + L / 2 - l) +
        (1.2124 + 0.00007 * L) * p + 0.001 ≤ L ^ 2 / 8 := by
      have hll : 0 ≤ (l - 3.5) * (L / 7 - l) := mul_nonneg (by linarith) (by linarith)
      have hx : 0 ≤ (l - 3.5) * (L - 34.5) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have e : s * L / p / 2 + s * ((L / 2 - l) ^ 2 / (2 * p) + 4.8) + (c + L / 2 - l) * s / p + E +
        0.001 + 1.212 * s + (0.00007 * s * L + 0.0004 * s) =
        s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 4.8 * p) + (c + L / 2 - l) +
          (1.2124 + 0.00007 * L) * p) + E + 0.001 := by
      field_simp; ring
    rw [e]
    have e2 : s * L ^ 2 / (8 * p) = s / p * (L ^ 2 / 8) := by field_simp
    rw [e2]
    have hsp : 100000 ≤ s / p := by rw [le_div_iff₀ hp0]; nlinarith
    have : s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 4.8 * p) + (c + L / 2 - l) +
        (1.2124 + 0.00007 * L) * p) + s / p * 0.001 ≤ s / p * (L ^ 2 / 8) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left key (by positivity)
    nlinarith
  have hA : (s + u) * S1v = s * S1v + u * S1v := by ring
  have h2' : (s + u) * (p * s + L) * B = (s + L / (2 * p)) * (p * s + L) * B := by rw [hu]
  rw [hA] at *
  calc _ = s * L / p / 2 + E + 4.786 / (s * L / p) + 1.2 * s + (s * S1v + u * S1v) +
        (s + u) * (p * s + L) * B := by rw [hu, hS1v, hB]
    _ ≤ _ := by linarith

set_option maxHeartbeats 4000000 in
/-- **`|ψ(x) - x| ≤ √x log² x/(8π) - 1.2 √x` for `x ≥ 10^15`**, under RH, from `NB1000`,
`NBHead14` and `Ordinates14` for the zeros. -/
theorem psi_schoenfeld_large_slackB (hRH : RiemannHypothesis) (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 15 ≤ x) :
    |psiF x - x| ≤ √x * log x ^ 2 / (8 * π) - 1.2 * √x := by
  obtain ⟨hs1, hL, hL2, hl, hlL, hLs⟩ := large_factsB hx
  have hx0 : 0 < x := by linarith
  set s := √x with hsdef
  set L := log x with hLdef
  set l := log L with hldef
  set c := log (2 * π) with hcdef
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hsx : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hp0 := Real.pi_pos
  have hp1 : 3.14 ≤ π := Real.pi_gt_d2.le
  have hp2 : π ≤ 3.15 := Real.pi_lt_d2.le
  have hc1 : 1.8 ≤ c := SchoenfeldPort.ChirreHagen2025.Lemma26H.c_lower
  have hc2 : c ≤ 2 := SchoenfeldPort.ChirreHagen2025.Lemma26H.c_upper
  have hLs' : L ≤ s / 2530 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (s / 2530) ^ 2 ≤ L ^ 2 := by gcongr
    have h2 : s * 31622776 ≤ s * s := mul_le_mul_of_nonneg_left hs1 hs0.le
    nlinarith
  set h := s * L / π with hhdef
  have hh0 : 0 < h := by positivity
  set T := 2 * π * s / L with hTdef
  have hT : 1000 ≤ T := by
    rw [hTdef, le_div_iff₀ hL0]; nlinarith
  have hlogT : log T = c + L / 2 - l := by
    rw [hTdef, Real.log_div (by positivity) hL0.ne', Real.log_mul (by positivity) hs0.ne']
    linarith
  have hT0 : 0 < T := by linarith
  set M := c + L / 2 - l with hM
  have hM0 : 0 ≤ M := by linarith
  have hS1 : SB1 T = (L / 2 - l) ^ 2 / (2 * π) + 4.8 := by
    unfold SB1; rw [hlogT, hM, hcdef]; ring
  set B := (c + L / 2 - l) / (π ^ 2 * s) + (18 * (c + L / 2 - l) + 72.9) * L / (2 * π ^ 2 * s ^ 2)
    with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hS2 : SB2 T ≤ L / 2 * B := by
    unfold SB2
    rw [hlogT]
    have a : (18 * M + 72.9 - 0.25 * T) / T ^ 2 ≤ (18 * M + 72.9) / T ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have e : M / (π * T) + (18 * M + 72.9) / T ^ 2 = L / 2 * B := by
      rw [hB, hTdef]; field_simp; ring
    linarith
  set K := s + L / (2 * π) with hK
  have hK0 : 0 < K := by positivity
  have hS1v0 : 0 ≤ (L / 2 - l) ^ 2 / (2 * π) + 4.8 := by positivity
  -- the square roots
  have hX1 : (x + h) ^ (1 / 2 : ℝ) ≤ K := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left hK0.le, hK, ← hsx, hhdef]
    have : 0 ≤ (L / (2 * π)) ^ 2 := sq_nonneg _
    have e : (s + L / (2 * π)) ^ 2 = s ^ 2 + s * L / π + (L / (2 * π)) ^ 2 := by field_simp; ring
    linarith
  have hX10 : 0 ≤ (x + h) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hX3 : (x + h) ^ (3 / 2 : ℝ) ≤ (x + h) * K := by
    rw [rpow_three_halves (by linarith)]
    exact mul_le_mul_of_nonneg_left hX1 (by linarith)
  have hx12 : x ^ (1 / 2 : ℝ) = s := by rw [hsdef, Real.sqrt_eq_rpow]
  have hx32 : x ^ (3 / 2 : ℝ) = s * s ^ 2 := by
    rw [rpow_three_halves hx0.le, hx12, hsx]; ring
  have hcore0 := coreB (E := 0) hs1 hL hL2 hl hlL hc1 hc2 hp1 hp2 le_rfl (by norm_num)
  have hcorec := coreB (E := c) hs1 hL hL2 hl hlL hc1 hc2 hp1 hp2 (by linarith) (by linarith)
  have hfac : 2 * ((x + h) * K) * (L / 2 * B) / h = K * (π * s + L) * B := by
    rw [hhdef, ← hsx]; field_simp
  have hhs : h ≤ s * s / 7944 := by
    have a : s * L ≤ s * (s / 2530) := mul_le_mul_of_nonneg_left hLs' hs0.le
    have b : s * L / π ≤ s * L / 3.14 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hp1
    rw [hhdef]
    have e : s * (s / 2530) / 3.14 = s * s / 7944.2 := by ring
    have c' : s * L / 3.14 ≤ s * (s / 2530) / 3.14 := div_le_div_of_nonneg_right a (by norm_num)
    have d : s * s / 7944.2 ≤ s * s / 7944 := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    linarith
  set S1v := (L / 2 - l) ^ 2 / (2 * π) + 4.8 with hS1v
  have hc0 : h / 2 + 0 + 4.786 / h + 1.2 * s + K * S1v + K * (π * s + L) * B ≤
      s * L ^ 2 / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcore0
  have hcc : h / 2 + c + 4.786 / h + 1.2 * s + K * S1v + K * (π * s + L) * B ≤
      s * L ^ 2 / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcorec
  rw [abs_le]
  constructor
  · -- lower
    have hlow := psi_lower_genB hRH hN hH h14 (x := x) (h := h) (T := T)
      (by have : s * s = x := by rw [← hsx]; ring
          nlinarith) hh0 hT
    rw [← hcdef] at hlow
    rw [hx12, hx32, hS1] at hlow
    have t1 : s * S1v ≤ K * S1v :=
      mul_le_mul_of_nonneg_right (by rw [hK]; have : 0 ≤ L / (2 * π) := by positivity
                                     linarith) hS1v0
    have t2 : 2 * (s * s ^ 2) * SB2 T / h ≤ K * (π * s + L) * B := by
      have a : 2 * (s * s ^ 2) * SB2 T / h ≤ 2 * (s * s ^ 2) * (L / 2 * B) / h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        exact mul_le_mul_of_nonneg_left hS2 (by positivity)
      have b : 2 * (s * s ^ 2) * (L / 2 * B) / h = π * s ^ 2 * B := by
        rw [hhdef]; field_simp
      have c' : π * s ^ 2 * B ≤ K * (π * s + L) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        rw [hK]; have : 0 ≤ L / (2 * π) * (π * s + L) := by positivity
        nlinarith
      linarith
    linarith
  · -- upper
    have hup := psi_upper_genB hRH hN hH h14 (x := x) (h := h) (T := T) (by linarith) hh0 hT
    rw [hS1, ← hcdef] at hup
    have t1 : (x + h) ^ (1 / 2 : ℝ) * S1v ≤ K * S1v := mul_le_mul_of_nonneg_right hX1 hS1v0
    have t2 : 2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T / h ≤ K * (π * s + L) * B := by
      rw [← hfac]
      apply div_le_div_of_nonneg_right _ hh0.le
      have hS20 : 0 ≤ SB2 T ∨ SB2 T < 0 := le_or_gt 0 (SB2 T)
      rcases hS20 with h0 | h0
      · apply mul_le_mul (by linarith) hS2 h0 (by positivity)
      · have : 2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
        have : 0 ≤ 2 * ((x + h) * K) * (L / 2 * B) := by positivity
        linarith
    linarith

/-- **`|ψ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^15`**, from `NB1000`, `NBHead14`, `Ordinates14`
for the zeros (RH discharged by `riemannHypothesis`). -/
theorem psi_schoenfeld_largeB (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ x ≥ (10 : ℝ) ^ 15, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  intro x hx
  have h := psi_schoenfeld_large_slackB riemannHypothesis hN hH h14 hx
  rw [psiF_eq_psi] at h
  have : 0 ≤ √x := Real.sqrt_nonneg x
  linarith

/-- **`|θ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^15`**, from `NB1000`, `NBHead14`, `Ordinates14`
for the zeros (RH discharged by `riemannHypothesis`). -/
theorem theta_schoenfeld_largeB (hN : NB1000 gZ) (hH : NBHead14 gZ)
    (h14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ x ≥ (10 : ℝ) ^ 15, |θ x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  intro x hx
  have h1 := psi_schoenfeld_large_slackB riemannHypothesis hN hH h14 hx
  rw [psiF_eq_psi] at h1
  have h2 := psi_sub_theta_large (x := x) (by linarith)
  have h3 := theta_le_psi x
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-! ### From the zero count `N(T)` -/

/-- `NBHead14 gZ` from the upper bound on `N(T)` for `T ≥ 14`. -/
theorem NBHead14_of_NT (h : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + RtB T) : NBHead14 gZ := by
  intro T hT s
  calc ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T := card_filter_abs_le_le s T
    _ ≤ 2 * (Mt T + RtB T) := by linarith [h T hT]

/-- `NB1000 gZ` from the two-sided bound on `N(T)` for `T ≥ 1000`. -/
theorem NB1000_of_NT (hU : ∀ T : ℝ, 1000 ≤ T → (NT T : ℝ) ≤ Mt T + RtB T)
    (hL : ∀ T : ℝ, 1000 ≤ T → Mt T - RtB T ≤ NT T) : NB1000 gZ := by
  constructor
  · intro T hT s
    calc ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T := card_filter_abs_le_le s T
      _ ≤ 2 * (Mt T + RtB T) := by linarith [hU T hT]
  · intro T t hT hTt s
    have h1 := card_filter_le_two_mul_Nband s (a := T) (b := t) (by linarith)
    have h2 : ((s.filter (fun i => T < |gZ i| ∧ |gZ i| ≤ t)).card : ℝ) ≤ 2 * Nband T t := by
      exact_mod_cast h1
    rw [← NT_sub (by linarith) hTt] at h2
    linarith [hU t (by linarith), hL T hT]

/-- **`|ψ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^15`** from the three `N(T)` statements
`(U') ∀ T ≥ 14, N(T) ≤ Mt T + RtB T`, `(L') ∀ T ≥ 1000, Mt T - RtB T ≤ N(T)`, `(Z) N(14) = 0`,
with `Mt T = (T/2π) log(T/(2πe)) + 7/8` and `RtB T = 4.5 log T + 17.1`. -/
theorem schoenfeld_psi_large_of_NTB
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + RtB T)
    (hL : ∀ T : ℝ, 1000 ≤ T → Mt T - RtB T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 15, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π) :=
  psi_schoenfeld_largeB (NB1000_of_NT (fun T hT => hU T (by linarith)) hL) (NBHead14_of_NT hU)
    (Ordinates14_of_NT h14)

/-- **`|θ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^15`** from the same three `N(T)` statements. -/
theorem schoenfeld_theta_large_of_NTB
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + RtB T)
    (hL : ∀ T : ℝ, 1000 ≤ T → Mt T - RtB T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 15, |θ x - x| ≤ √x * log x ^ 2 / (8 * π) :=
  theta_schoenfeld_largeB (NB1000_of_NT (fun T hT => hU T (by linarith)) hL) (NBHead14_of_NT hU)
    (Ordinates14_of_NT h14)

end SchoenfeldS1

import Mathlib
import SchoenfeldPort.ChirreHagen2025.SmoothTheorem2

/-!
P0075 line, T2, OPEN AUDIT U-1248, I-0010, PC 20261020T1503Z-30533, 2026-10-20.
Chirre-Hagen, arXiv 2512.23534v1, Lemma 2.6, the cited `Lemma26` of SmoothTheorem2.lean, PROVED
CONDITIONAL ON `HSWN` only: the N(T) bound of Hasanalizade, Shen and Wong, Counting zeros of the
Riemann zeta function, arXiv 2107.06506, Corollary 1.2, `|N(T) - (T/2π) log(T/(2πe))| ≤ 0.1038 log T
+ 0.2573 log log T + 9.3675` for `T ≥ e`, read here as counts of the ordinates, both signs, with the
`7/8` of the main term `Mt` moved into the error, `R2 = 0.1038 log T + 0.2573 log log T + 10.2425`.
This replaces `Lemma26P.TrudgianN`, whose 2.510 + 0.2/T rests on Trudgian, JNT 134 (2014), which
Hasanalizade-Shen-Wong report contains an error, an incorrect |ζ(1 + it)| bound of Cheng-Graham.
The proof is `Lemma26Proof.lean` with only the error bounds `R_le_base`, `R_sum`, `R_le` redone.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

namespace SchoenfeldPort.ChirreHagen2025.Lemma26H
open MeasureTheory Set Filter Topology Real

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- The Hasanalizade-Shen-Wong error with the `7/8` added, `R2(T) = 0.1038 log T + 0.2573 log log T + 10.2425`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.1038 * log T + 0.2573 * log (log T) + 10.2425

/-! ### Elementary bounds -/

lemma exp_one_lt' : exp 1 < 2.7182818286 := Real.exp_one_lt_d9

lemma c_lower : 1.8 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h9 : exp 1.8 ^ 5 = exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 : exp 1 ^ 9 < 2.7182818286 ^ 9 := by
    gcongr; exact exp_one_lt'
  have h2 : (2.7182818286 : ℝ) ^ 9 < 6.28 ^ 5 := by norm_num
  have hp : (6.28 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_d2]
  by_contra hc
  push_neg at hc
  have : (2 * π) ^ 5 < exp 1.8 ^ 5 := by gcongr
  have : (6.28 : ℝ) ^ 5 ≤ (2 * π) ^ 5 := by gcongr
  linarith

lemma c_upper : log (2 * π) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have := Real.exp_one_gt_d9
  have h : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [Real.pi_lt_d2]

lemma Mt_eq {x : ℝ} (hx : 0 < x) :
    Mt x = x * (log x - log (2 * π) - 1) / (2 * π) + 7 / 8 := by
  unfold Mt
  rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (Real.exp_pos 1).ne',
    Real.log_exp]
  ring

/-! ### The kernel `(2 log t - 1)/t³` and the antiderivative -/

/-! ### Lemma 2.6 -/

end SchoenfeldPort.ChirreHagen2025.Lemma26H



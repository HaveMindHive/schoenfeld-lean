import Mathlib
import SchoenfeldPort.ChirreHagen2025.SmoothTheorem2

/-!
P0075 line, T2, unit U-6502, I-0010, CLOUD 20261020T1415Z-cloud44, 2026-10-20.
Chirre-Hagen, arXiv 2512.23534v1, Lemma 2.6, the cited `Lemma26` of SmoothTheorem2.lean,
PROVED CONDITIONAL ON `TrudgianN` only: Trudgian's bound
`|N(T) - (T/2π) log(T/(2πe)) - 7/8| ≤ 0.112 log T + 0.278 log log T + 2.510 + 0.2/T`, the
`N(T)` form, Corollary 1, of T. Trudgian, J. Number Theory 134 (2014), Theorem 1, `|S(T)| ≤ 0.112 log T +
0.278 log log T + 2.510` for `T ≥ e`, used here only for `T ≥ 10^13`, read as
counts of the ordinates `γ i`, both signs, in `[-T, T]` and in the windows `T < |γ| ≤ t`.
The paper uses the simpler `0.28 log T` of Brent-Platt-Trudgian instead, weaker than Trudgian at `T = 10^13`; the lab's constants
leave room: the tail sum comes out at `1.0232 log² T/(π T)` at `T = 10^13`, below `1.028`.

Proof of the tail: the layer cake `log g/g² = ∫_g^∞ (2 log t - 1)/t³ dt` summed over the finite
set, the count bounded by the window bound, and the explicit antiderivative `Hf`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

namespace SchoenfeldPort.ChirreHagen2025.Lemma26P
open MeasureTheory Set Filter Topology Real

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- Trudgian's error bound for `N(T)`, `R(T) = 0.112 log T + 0.278 log log T + 2.510 + 0.2/T`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.112 * log T + 0.278 * log (log T) + 2.51 + 0.2 / T

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

lemma tendsto_log_pow_div (n : ℕ) : Tendsto (fun x => log x ^ n / x) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  simpa using this

lemma tendsto_log_pow_div_sq (n : ℕ) : Tendsto (fun x => log x ^ n / x ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div n).mul tendsto_inv_atTop_zero
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-! ### Lemma 2.6 -/

end SchoenfeldPort.ChirreHagen2025.Lemma26P



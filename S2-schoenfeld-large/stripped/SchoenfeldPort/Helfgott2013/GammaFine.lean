import Mathlib
import SchoenfeldPort.ChenExplicit.GammaBounds

/-!
P0001 Helfgott 2013, Section 7.3, pages 64 to 67: sharper two-sided bounds on Euler's
constant, `0.5772143 < γ < 0.57721567`, and on `e^γ`, for the constants `F(r₀) ≤ 5.42506`,
`(7.40)` and `(7.42)`, which are sensitive to `γ` at the `10⁻⁷` level.
The lab's `ChenExplicit.Gamma` gives `0.57720 < γ < 0.57722`, not enough here.

Method. Lower: `u 256 = H_256 - 8 log 2 - 1/512 ≤ γ` from `ChenExplicit.Gamma.u_le_gamma`.
Upper: `W n = H_n - log(n + 1/2) - c/(n + 1/2)²` with `24c = 1 - 10⁻⁴` decreases for `n ≥ 121`,
because `log(1 + 1/a) ≥ 2y + 2y³/3`, `y = 1/(2a + 1)`, and `24c m⁴ ≤ (m² - 1/4)²` for `m ≥ 122`;
and `W n → γ`. Then `W 121` with `log 121.5 = 4 log 2 + 5 log(3/2)`.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is Helfgott's theorem.
-/

open Real Filter Topology Finset

noncomputable section
namespace SchoenfeldPort.Helfgott2013.GammaFine

open SchoenfeldPort.ChenExplicit.Gamma

/-- The correction constant, `24c = 1 - 10⁻⁴`. -/
def cW : ℝ := (1 - 1 / 10000) / 24

/-- `W n = H_n - log(n + 1/2) - c/(n + 1/2)²`. -/
def W (n : ℕ) : ℝ := harmonic n - log (n + 1 / 2) - cW / ((n : ℝ) + 1 / 2) ^ 2

/-- `log(1 + 1/a) ≥ 2y + 2y³/3`, the first two terms of the series. -/
lemma log_two_terms {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ log (1 + a⁻¹) := by
  have h := log_one_add_inv_ge_sum ha 2
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h
  rw [one_div, inv_pow]
  linarith

lemma W_step (n : ℕ) (hn : 121 ≤ n) : W (n + 1) ≤ W n := by
  unfold W
  have hn' : (121 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0 : ℝ) < n + 1 / 2 := by positivity
  have hl := log_two_terms ha
  have e1 : log (((n + 1 : ℕ) : ℝ) + 1 / 2) = log (n + 1 / 2) + log (1 + ((n : ℝ) + 1 / 2)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]; congr 1; push_cast; field_simp; ring
  rw [e1, harmonic_succ]; push_cast
  have key : cW / ((n : ℝ) + 1 / 2) ^ 2 - cW / ((n : ℝ) + 1 + 1 / 2) ^ 2 ≤
      2 / 3 * (1 / (2 * ((n : ℝ) + 1 / 2) + 1)) ^ 3 := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    rw [show (2 : ℝ) / 3 * (1 / (2 * ((n : ℝ) + 1 / 2) + 1)) ^ 3 = 1 / (12 * ((n : ℝ) + 1) ^ 3) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold cW
    have hs : (14884 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2)
      (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 / 10000 - 1 / 2)]
  have hy : 2 * (1 / (2 * ((n : ℝ) + 1 / 2) + 1)) = ((n : ℝ) + 1)⁻¹ := by field_simp; ring
  linarith

lemma W_anti (n k : ℕ) (hn : 121 ≤ n) : W (n + k) ≤ W n := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (W_step (n + k) (by omega)) ih

lemma W_tendsto : Tendsto W atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := w_tendsto
  have h2 : Tendsto (fun n : ℕ => cW / ((n : ℝ) + 1 / 2) ^ 2) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 2) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact h3.const_div_atTop _ |>.congr' (Eventually.of_forall fun _ => rfl)
  have := h1.sub h2
  rw [sub_zero] at this
  exact this.congr fun n => by simp [W, w]

theorem gamma_le_W121 : eulerMascheroniConstant ≤ W 121 := by
  apply le_of_tendsto W_tendsto
  filter_upwards [eventually_ge_atTop 121] with m hm
  have := W_anti 121 (m - 121) le_rfl
  rwa [show 121 + (m - 121) = m by omega] at this

theorem harmonic_121_lt : harmonic 121 < (5377132750164 / 1000000000000 : ℚ) := by
  decide +kernel

/-- `log(3/2) ≥ 0.4054651081`, five terms of the series at `a = 2`. -/
theorem log_three_halves_gt : (0.4054651080 : ℝ) < log (3 / 2) := by
  have h := log_one_add_inv_ge_sum (a := (2 : ℝ)) (by norm_num) 8
  simp only [sum_range_succ, sum_range_zero] at h
  have e : (1 : ℝ) + (2 : ℝ)⁻¹ = 3 / 2 := by norm_num
  rw [e] at h
  norm_num at h
  linarith

/-- **`γ < 0.57721567`, PROVED**, from `W 121 ≈ 0.5772156652`. -/
theorem gamma_lt_fine : eulerMascheroniConstant < (0.57721567 : ℝ) := by
  have h := gamma_le_W121
  unfold W cW at h
  have hH : (harmonic 121 : ℝ) < ((5377132750164 / 1000000000000 : ℚ) : ℝ) := by
    exact_mod_cast harmonic_121_lt
  have l2 := log_two_gt_d9
  have l3 := log_three_halves_gt
  have e : log (((121 : ℕ) : ℝ) + 1 / 2) = 4 * log 2 + 5 * log (3 / 2) := by
    have : (((121 : ℕ) : ℝ) + 1 / 2) = 2 ^ 4 * (3 / 2) ^ 5 := by norm_num
    rw [this, log_mul (by norm_num) (by norm_num), log_pow, log_pow]; push_cast; ring
  rw [e] at h
  push_cast at h hH
  norm_num at h hH l2 ⊢
  linarith

end SchoenfeldPort.Helfgott2013.GammaFine



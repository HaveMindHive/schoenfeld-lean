import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
Two-sided bounds on Euler's constant, `0.57720 < γ < 0.57722`, for the Section 9 margin of
P0009, BJS 2022, which is sensitive to `γ` at the `10⁻⁵` level. Mathlib has `1/2 < γ < 2/3`.

Method: `u n = H_n - log n - 1/(2n)` increases to `γ` and `w n = H_n - log(n + 1/2)` decreases
to `γ`; both steps come from Mathlib's series `log(1 + 1/a) = 2 Σ y^{2k+1}/(2k+1)`,
`y = 1/(2a + 1)`. Then `u 100` and `w 100` are evaluated from `H_100` and `log 2`, `log(5/4)`.
-/

open Real Filter Topology Finset

noncomputable section
namespace SchoenfeldPort.ChenExplicit.Gamma

/-- `log(1 + 1/a)` up to the first `n` terms, lower bound. -/
lemma log_one_add_inv_ge_sum {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∑ k ∈ range n, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
      log (1 + a⁻¹) :=
  sum_le_hasSum _ (fun k _ => by positivity) (hasSum_log_one_add_inv ha)

/-- `w n = H_n - log(n + 1/2)`. -/
def w (n : ℕ) : ℝ := harmonic n - log (n + 1 / 2)

lemma w_tendsto : Tendsto w atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => log ((n : ℝ) + 1 / 2) - log n) atTop (𝓝 0) := by
    have := tendsto_log_comp_add_sub_log (1 / 2 : ℝ)
    exact this.comp tendsto_natCast_atTop_atTop
  have := h1.sub h2
  simp only [sub_zero] at this
  refine this.congr fun n => ?_
  simp [w]

end SchoenfeldPort.ChenExplicit.Gamma


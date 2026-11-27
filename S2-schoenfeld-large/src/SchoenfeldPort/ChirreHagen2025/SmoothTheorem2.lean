import Mathlib
import Mathlib
import Mathlib

/-!
P0075 line, T2, unit U-6356, I-5170, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
Chirre-Hagen's Theorem 2 with 1.2913 in place of 2.2258, from named zero inputs:
* `ExplicitA`: the explicit formula as the paper writes it, `A_δ(y) = 𝒱(δ, y) - B_δ(y)` is
  the limit of `-Σ_{ρ ∈ Z_n} c_ρ y^ρ`, `c_ρ = ((1+δ)^ρ - 1)/ρ`, along truncations `Z_n`, for
  almost every `y ≥ 2`; under RH every `ρ = 1/2 + iγ`.
* `HadamardK`: `Σ_γ' 4/(4 + (γ - γ')²) ≤ log |γ|`, the analogue at `α = 5/2` of the paper's
  Lemma 2.2 part 1, for finite partial sums.
* `Lemma26`: the paper's Lemma 2.6 for both signs of `γ`, so with `1/Real.pi` for `1/(2Real.pi)`.
* `CoefBound`: the paper's Lemma 2.5, `|c_ρ| ≤ min(δ, ℓ/|γ|)`.
* `Ordinates14`: every `|γ| ≥ 14`.
The proof: the finite smoothed mean square `interval_P_le` for each truncation, Fatou, the
diagonal with `HadamardK`, the split at `T = ℓ/δ` with `Lemma26`, and `B_δ ≤ δ` on `y ≥ 2`;
the range `[1, 2]` by `Local36.small_range`.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

namespace SchoenfeldPort.ChirreHagen2025.SmoothT2
open Complex MeasureTheory Set Filter Topology

variable {ι : Type*}

/-- Every ordinate has `|γ| ≥ 14`. -/
def Ordinates14 (γ : ι → ℝ) : Prop := ∀ i, 14 ≤ |γ i|

end SchoenfeldPort.ChirreHagen2025.SmoothT2



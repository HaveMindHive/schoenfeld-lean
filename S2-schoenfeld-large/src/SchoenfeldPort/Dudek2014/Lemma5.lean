import Mathlib
import SchoenfeldPort.Dudek2014.Display

/-!
P0100 Dudek 2014, page 4: identity (5) and Lemma 5 from Lemma 4.
- (5): `Σ Λ(n) w(n) = (ψ₁(x + h) - 2ψ₁(x) + ψ₁(x - h))/h`, `ψ₁(y) = Σ_{n≤y} (y - n) Λ(n)`,
  PROVED for `0 < h ≤ x`, from the pointwise identity
  `h w(n) = (x + h - n)₊ - 2(x - n)₊ + (x - h - n)₊`.
- Lemma 5 from Lemma 4: with `ψ₁(y) = y²/2 - Z(y) - y log 2π + ε(y)` and `|ε(y)| ≤ 2.393`,
  the second difference gives `Σ Λ w = h - Σ/h + ε(h)`, `|ε(h)| ≤ 4 · 2.393/h < 48/(5h)`,
  with `Σ = Z(x+h) - 2Z(x) + Z(x-h)`, the paper's zero sum. The cited Lemma 4 is taken for all
  `y > 0` with the paper's computed constant `2 + 2^{3/2}(2 + γ - log 4π) + (1/2) log(27/16)
  < 2.393` (`lemma4_const` pieces), the continuous extension of the paper's non-integer case.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

namespace SchoenfeldPort.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `ψ₁(y) = Σ_{n ≤ y} (y - n) Λ(n)`. -/
def psi1 (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, (y - n) * Λ n

theorem psi1_ext {y : ℝ} (hy : 0 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ n ∈ Iic N, max (y - n) 0 * Λ n = psi1 y := by
  unfold psi1
  rw [← Iic_union_Ioc_eq_Iic hN, sum_union (Iic_disjoint_Ioc le_rfl)]
  have h2 : ∑ n ∈ Ioc ⌊y⌋₊ N, max (y - n) 0 * Λ n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_Ioc] at hn
    have : y < n := by
      have := Nat.lt_floor_add_one y
      have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
      push_cast at this; linarith
    rw [max_eq_right (by linarith), zero_mul]
  rw [h2, add_zero]
  apply sum_congr rfl
  intro n hn
  rw [mem_Iic] at hn
  have : (n : ℝ) ≤ y := by
    have := Nat.floor_le hy
    have : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn
    linarith
  rw [max_eq_left (by linarith)]

end

end SchoenfeldPort.Dudek2014.Section22



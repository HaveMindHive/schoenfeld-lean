import SchoenfeldPort.PNTPort.ExplicitPsi1.DudekTrudgian
import SchoenfeldPort.Dudek2014.Display

/-!
# From `ψ₁` to `ψ`: unsmoothing, and an explicit `ψ(x) = x + O(x^{3/4})` under RH

I-5190, unit U-6603, CLOUD 20261020T1618Z-cloud46. AI wrote this file. Known mathematics.

* `psi1_diff_bounds`: for `0 ≤ x` and `0 < h`, `h ψ(x) ≤ ψ₁(x + h) - ψ₁(x) ≤ h ψ(x + h)`, since
  `ψ₁(y) = Σ_{n ≤ y} (y - n) Λ(n)` and each weight grows by at most `h`, exactly `h` for `n ≤ x`;
* `psi_RH_34`: under RH and Trudgian 2014's `N(T)` bound, from cloud45's `psi1_RH_simple`,
  `|ψ₁(y) - y²/2| ≤ 133 y^{3/2}`, with `h = 32 x^{3/4}`:
  `|ψ(x) - x| ≤ 32 x^{3/4}` for every `x ≥ 64⁴`.
The exponent is the trivial one from one unsmoothing; Schoenfeld's `√x log² x / 8π` needs the
truncated explicit formula for `ψ` itself. Binary Goldbach is OPEN.
-/

namespace SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial

open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open SchoenfeldPort.Dudek2014.Section22

/-- **Unsmoothing.** `h ψ(x) ≤ ψ₁(x + h) - ψ₁(x) ≤ h ψ(x + h)`. -/
theorem psi1_diff_bounds {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    h * psiF x ≤ psi1 (x + h) - psi1 x ∧ psi1 (x + h) - psi1 x ≤ h * psiF (x + h) := by
  set M := ⌊x + h⌋₊ with hM
  have hxM : ⌊x⌋₊ ≤ M := Nat.floor_le_floor (by linarith)
  have e1 := psi1_ext (show 0 ≤ x + h by linarith) (le_refl M)
  have e0 := psi1_ext hx hxM
  have hdiff : psi1 (x + h) - psi1 x =
      ∑ n ∈ Iic M, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
    rw [← e1, ← e0, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => by ring
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · -- lower: the terms with n ≤ ⌊x⌋ have weight exactly h
    rw [hdiff]
    have hsub : Iic ⌊x⌋₊ ⊆ Iic M := Iic_subset_Iic.2 hxM
    have hpsi : h * psiF x = ∑ n ∈ Iic ⌊x⌋₊, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
      unfold psiF
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      rw [mem_Iic] at hn
      have hn' : (n : ℝ) ≤ x := by
        have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
        exact this.trans (Nat.floor_le hx)
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [hpsi]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro n _ _
    apply mul_nonneg _ (hΛ n)
    have : max (x - n) 0 ≤ max (x + h - n) 0 := max_le_max (by linarith) le_rfl
    linarith
  · -- upper: every weight grows by at most h
    rw [hdiff]
    unfold psiF
    rw [← hM, mul_sum]
    refine sum_le_sum fun n _ => ?_
    apply mul_le_mul_of_nonneg_right _ (hΛ n)
    rcases le_total (x - n) 0 with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total (x + h - n) 0 with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_left (by linarith)]; linarith

end SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial


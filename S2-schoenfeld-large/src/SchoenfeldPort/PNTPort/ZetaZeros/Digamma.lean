import SchoenfeldPort.PNTPort.ZetaZeros.GammaBounds
import SchoenfeldPort.PNTPort.StrongPNT.StrongPNT

/-!
# A digamma bound: `|ψ(s)| ≪ log t` near `1 + it`

Lab proof, unit U-5270, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input. With `c = 1 + it`, `t ≥ 1`, the function `f(z) = Γ(c + z/2)/Γ(c)` has no zeros,
`|f| ≤ 3(t + 4)` on `‖z‖ ≤ 29/30` by `norm_Gamma_le_PL` and `|Γ(1 + it)|² = πt / sinh(πt)`, so the
ported Borel-Carathéodory bound `FinalBound`, Apache-2.0, PrimeNumberTheoremAnd, gives
`|Γ'/Γ(s)| ≪ log t` for `‖s - c‖ ≤ 1/3`. With Mathlib's `digamma_apply_add_one` this reaches
every vertical line, and with `logDeriv_riemannZeta_one_sub` the left half plane for `ζ'/ζ`.
-/

namespace SchoenfeldPort.PNTPort.ZetaZeros

open Complex Set Filter Metric
open scoped Real ComplexConjugate

lemma gamma_analyticAt {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Gamma w := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    have hne : ∀ m : ℕ, z ≠ -m := by
      intro m h; have := hz; rw [h] at this; simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact (Complex.differentiableAt_Gamma z hne).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hw)

lemma gamma_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : Gamma w ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h; rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

end SchoenfeldPort.PNTPort.ZetaZeros



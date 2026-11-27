import SchoenfeldPort.PNTPort.ExplicitPsi1.Nontrivial

/-!
# The constant term is `log 2π`

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input: `ζ'(0)/ζ(0) = log 2π` from Mathlib's `deriv_riemannZeta_zero` and
`riemannZeta_zero`, so the explicit formula reads, for every `x > 0`,
`|Σ Λ(n) max(0, 1 - n/x) - x/2 + log 2π + Σ_ρ m(ρ) x^ρ/(ρ(ρ + 1))| ≤ K x^{-1/2}`,
the sum over the nontrivial zeros.
-/

namespace SchoenfeldPort.PNTPort.ExplicitPsi1

open Complex
open scoped Real

theorem logDeriv_zeta_zero : deriv riemannZeta 0 / riemannZeta 0 = Real.log (2 * π) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity)]
  field_simp

end SchoenfeldPort.PNTPort.ExplicitPsi1



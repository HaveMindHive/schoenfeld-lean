/-
Schoenfeld S1, part H: the final theorems. Schoenfeld's bounds
`|ψ(x) - x| ≤ √x log² x/(8π)` and `|θ(x) - x| ≤ √x log² x/(8π)` for every `x ≥ 10^15`, with no
hypothesis beyond the proven Riemann hypothesis of the repository (`riemannHypothesis`, Alpöge with
Claude): (U') and (L') from `SchoenfeldS1.C`, `N(14) = 0` from `SchoenfeldS1.Z`, the port's
`schoenfeld_psi_large_of_NTB` / `schoenfeld_theta_large_of_NTB` through `SchoenfeldS1.G`.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti). Apache-2.0.
-/
import SchoenfeldS1.C

namespace SchoenfeldS1

open Real

/-- Schoenfeld's bound for `x ≥ 10^15` from `N(14) = 0` alone. -/
theorem schoenfeld_psi_large_of_Z (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_psi_large_of_NTB (fun _ hT => NT_le_Mt_add_RtB hT) (fun _ hT => Mt_sub_RtB_le_NT hT) h14

/-- **Schoenfeld's bound, unconditional on the proven Riemann hypothesis**:
`|ψ(x) - x| ≤ √x log² x/(8π)` for every `x ≥ 10^15`. -/
theorem schoenfeld_psi :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_psi_large_of_Z NT_fourteen_eq_zero

/-- **Schoenfeld's bound for `θ`**: `|θ(x) - x| ≤ √x log² x/(8π)` for every `x ≥ 10^15`. -/
theorem schoenfeld_theta :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.theta x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_theta_large_of_NTB (fun _ hT => NT_le_Mt_add_RtB hT) (fun _ hT => Mt_sub_RtB_le_NT hT)
    NT_fourteen_eq_zero

end SchoenfeldS1

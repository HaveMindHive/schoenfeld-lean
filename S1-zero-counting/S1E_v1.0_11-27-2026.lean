/-
Schoenfeld S1, part E: the final theorems conditional only on the zero count `N(T)`.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the ported
goldbach-lean modules (SchoenfeldPort, Steve Hubbard, Apache-2.0), Mathlib 31ce06ea and Tau Ceti,
in the environment of the riemann-hypothesis-community repository (Lean v4.37.0-rc1), whose
`riemannHypothesis` (Alpöge with Claude) discharges RH. Apache-2.0.
-/
import SchoenfeldS1.A

/-!
# Schoenfeld's bounds from three statements about `N(T)`

`SchoenfeldPort.schoenfeld_psi_large` and `schoenfeld_theta_large` restated with the counting
bridge of `SchoenfeldS1.A`: the only remaining inputs are, for the classical zero count
`NT T` (zeros of `ζ` in the open critical strip with `0 < Im ρ ≤ T`, with multiplicity),

* `N(T) ≤ Mt T + Rt T` for `T ≥ 14`,
* `Mt T - Rt T ≤ N(T)` for `T ≥ 70`,
* `N(14) = 0`,

with `Mt T = (T/2π) log (T/(2πe)) + 7/8` and `Rt T = 0.1038 log T + 0.2573 log log T + 10.2425`.
-/

namespace SchoenfeldS1

open Real Chebyshev
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt Rt)

/-- **`|ψ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 10^11`**, given the three `N(T)` statements. -/
theorem schoenfeld_psi_large_of_NT
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T)
    (hL : ∀ T : ℝ, 70 ≤ T → Mt T - Rt T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 11, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π) :=
  SchoenfeldPort.schoenfeld_psi_large
    ⟨HSWN70_of_NT (fun T hT => hU T (by linarith)) hL, HSWHead14_of_NT hU, Ordinates14_of_NT h14⟩

/-- **`|θ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 10^11`**, given the three `N(T)` statements. -/
theorem schoenfeld_theta_large_of_NT
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T)
    (hL : ∀ T : ℝ, 70 ≤ T → Mt T - Rt T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 11, |θ x - x| ≤ √x * log x ^ 2 / (8 * π) :=
  SchoenfeldPort.schoenfeld_theta_large
    ⟨HSWN70_of_NT (fun T hT => hU T (by linarith)) hL, HSWHead14_of_NT hU, Ordinates14_of_NT h14⟩

end SchoenfeldS1

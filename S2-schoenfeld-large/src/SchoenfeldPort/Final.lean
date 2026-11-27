/-
Copyright 2026 Steve Hubbard (goldbach-lean). Ported 11-27-2026 to Lean v4.37.0-rc1 and
Mathlib 31ce06ea, checked against the riemann-hypothesis-community repository.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Main
import SchoenfeldPort.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge

/-!
# Schoenfeld-shape bounds for `ψ` and `θ` for `x ≥ 10^11`, RH discharged

`riemannHypothesis` (module `Main` of the riemann-hypothesis-community repository) supplies the
`RiemannHypothesis` input of goldbach-lean's `psi_schoenfeld_large` and `theta_schoenfeld_large`.
What remains as hypotheses are three statements about `gZ`, the ordinates of the nontrivial
zeros of ζ listed with multiplicity: the zero-count bounds `HSWN70` and `HSWHead14`
(Hasanalizade-Shen-Wong, Corollary 1.2 shape) and `Ordinates14` (every ordinate has `|γ| ≥ 14`).
-/

namespace SchoenfeldPort

open Real Chebyshev
open SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)
open SchoenfeldPort.Dudek2014.SigmaH (HSWN70)
open SchoenfeldPort.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open SchoenfeldPort.ChirreHagen2025.SmoothT2 (Ordinates14)

/-- **`|ψ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 10^11`**, given the three zero-count statements. -/
theorem schoenfeld_psi_large (hZ : HSWN70 gZ ∧ HSWHead14 gZ ∧ Ordinates14 gZ) :
    ∀ x ≥ (10 : ℝ) ^ 11, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  intro x hx
  have h := PNTPort.ExplicitPsi1.Trivial.psi_schoenfeld_large riemannHypothesis hZ.1 hZ.2.1 hZ.2.2 hx
  rwa [PNTPort.ExplicitPsi1.Trivial.psiF_eq_psi] at h

/-- **`|θ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 10^11`**, given the three zero-count statements. -/
theorem schoenfeld_theta_large (hZ : HSWN70 gZ ∧ HSWHead14 gZ ∧ Ordinates14 gZ) :
    ∀ x ≥ (10 : ℝ) ^ 11, |θ x - x| ≤ √x * log x ^ 2 / (8 * π) :=
  fun _ hx => PNTPort.ExplicitPsi1.Trivial.theta_schoenfeld_large riemannHypothesis
    hZ.1 hZ.2.1 hZ.2.2 hx

/-- `ψ(x) - θ(x) ≤ 1.2 √x` for `x ≥ 10^11`, with no hypothesis. -/
theorem psi_sub_theta_large : ∀ x ≥ (10 : ℝ) ^ 11, ψ x - θ x ≤ 1.2 * √x :=
  fun _ hx => PNTPort.ExplicitPsi1.Trivial.psi_sub_theta_large hx

end SchoenfeldPort

-- The statements, exactly as the kernel holds them.
#check @SchoenfeldPort.schoenfeld_psi_large
#check @SchoenfeldPort.schoenfeld_theta_large
#print SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial.gZ
#print SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial.ZIdx
#print SchoenfeldPort.Dudek2014.SigmaH.HSWN70
#print SchoenfeldPort.PNTPort.ExplicitPsi1.FirstDiff.HSWHead14
#print SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14
#print SchoenfeldPort.ChirreHagen2025.Lemma26H.Mt
#print SchoenfeldPort.ChirreHagen2025.Lemma26H.Rt
#print axioms SchoenfeldPort.schoenfeld_psi_large
#print axioms SchoenfeldPort.schoenfeld_theta_large
#print axioms SchoenfeldPort.psi_sub_theta_large

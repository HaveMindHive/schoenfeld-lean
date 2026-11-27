import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import SchoenfeldPort.PNTPort.StrongPNT.Auxiliary
import SchoenfeldPort.PNTPort.StrongPNT.ZetaBounds
import SchoenfeldPort.PNTPort.StrongPNT.ZetaConj
import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib

/-! Ported to LeanLab from PrimeNumberTheoremAnd commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
   Apache License 2.0, original authors the PrimeNumberTheoremAnd project contributors.
   Changes: blueprint attributes and comments removed, import paths renamed, small fixes for
   Mathlib v4.35.0 listed in LeanLab/PNTPort/PLAN.md. This is reuse, not lab work. -/

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace Chebyshev

end Chebyshev

noncomputable abbrev ChebyshevPsi (x : ℝ) : ℝ :=
  Chebyshev.psi x

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in
theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-ζ' (σ₀ + t * I) / ζ (σ₀ + t * I))‖ ≤ ‖(ζ' σ₀ / ζ σ₀)‖ :=
  fun _ ↦ dlog_riemannZeta_bdd_on_vertical_lines_generalized _ _ _ σ₀_gt <| le_refl _

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by
  refine ⟨1 + ‖(ζ' σ₀ / ζ σ₀)‖, (by positivity), fun t ↦ ?_⟩
  have := dlog_riemannZeta_bdd_on_vertical_lines_explicit σ₀_gt t
  rw [neg_div, norm_neg] at this
  exact le_trans this (lt_one_add _).le

set_option maxHeartbeats 400000 in
-- Slow

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity

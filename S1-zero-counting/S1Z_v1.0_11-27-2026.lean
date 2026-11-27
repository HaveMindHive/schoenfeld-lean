/-
Schoenfeld S1, part Z: `N(14) = 0`.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the ported
goldbach-lean modules (SchoenfeldPort, Steve Hubbard, Apache-2.0), Mathlib 31ce06ea and Tau Ceti
(Apache-2.0), in the environment of the riemann-hypothesis-community repository (Lean v4.37.0-rc1),
whose `riemannHypothesis` (Levent Alpöge, with Claude) reduces the strip to the critical line.
Apache-2.0.
-/
import SchoenfeldS1.A
import SchoenfeldS1.ZGrid

/-!
# No zero of `ζ` of height in `(0, 14]`

* `NT_fourteen_eq_zero_of_line`: by the Riemann hypothesis (`riemannHypothesis`), every zero of
  `ζ` in the open critical strip has real part `1/2`, so `N(14) = 0` follows from
  `ζ(1/2 + it) ≠ 0` for `0 < t ≤ 14`.
* `SchoenfeldS1.Z.zeta_sl_ne_zero_of_le_fourteen` (module `SchoenfeldS1.ZGrid`): the latter, for
  `0 ≤ t ≤ 14`, by 49 generated interval certificates (Euler-Maclaurin of order 4 with 6 terms,
  certified rational enclosures, a Lipschitz bound on each interval).
* `NT_fourteen_eq_zero : NT 14 = 0`.
-/

namespace SchoenfeldS1

open Complex

/-- **The reduction to the critical line.** Under RH, `N(14) = 0` follows from the non-vanishing
of `ζ(1/2 + it)` for `0 < t ≤ 14`. -/
theorem NT_fourteen_eq_zero_of_line
    (h : ∀ t : ℝ, 0 < t → t ≤ 14 → riemannZeta (1 / 2 + t * I) ≠ 0) : NT 14 = 0 := by
  unfold NT Nband
  apply Finset.sum_eq_zero
  intro ρ hρ
  exfalso
  rw [mem_zerosBandF] at hρ
  obtain ⟨hz, h0, h1, hpos, hle⟩ := hρ
  have hre : ρ.re = 1 / 2 := by
    apply riemannHypothesis ρ hz
    · rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at h0
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rintro rfl; simp at h1
  have hρ : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  exact h ρ.im hpos hle (hρ ▸ hz)

/-- **`N(14) = 0`**: `ζ` has no zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 14`. -/
theorem NT_fourteen_eq_zero : NT 14 = 0 :=
  NT_fourteen_eq_zero_of_line fun t ht0 ht14 =>
    Z.zeta_sl_ne_zero_of_le_fourteen t ⟨ht0.le, ht14⟩

/-- `Ordinates14` for the ported theorem, now unconditional. -/
theorem ordinates14 : SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14
    SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial.gZ :=
  Ordinates14_of_NT NT_fourteen_eq_zero

end SchoenfeldS1

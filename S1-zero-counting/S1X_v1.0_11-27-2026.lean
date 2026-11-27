/-
Schoenfeld S1, part X: the entire function `xi s = s (s - 1) Λ₀(s) + 1`, its symmetries, zeros and
orders, for the Riemann-von Mangoldt identity (target (C)).
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldS1.A

/-!
# The completed function `xi`

`xi s = s (s - 1) Λ₀(s) + 1` where `Λ₀ = completedRiemannZeta₀` is Mathlib's entire modification of
`Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`; since `Λ = Λ₀ - 1/s - 1/(1 - s)`, `xi s = s (s - 1) Λ(s)` off `0, 1`
and `xi 0 = xi 1 = 1`. Facts: `xi` is entire, `xi (1 - s) = xi s`, `xi (conj s) = conj (xi s)`,
`xi σ > 0` on the real axis, `xi s ≠ 0` for `Re s ≥ 1` and for `Re s ≤ 0`, and in the open strip
`xi` has the zeros of `ζ` with the same orders.
-/

namespace SchoenfeldS1

open Complex Real ComplexConjugate
open SchoenfeldPort.PNTPort.ZetaZeros (zeta_one_sub_eq_zero)

local notation "ζ" => riemannZeta

/-- `xi s = s (s - 1) Λ₀(s) + 1`, Riemann's entire `ξ` up to the factor `1/2`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xi : Differentiable ℂ xi :=
  ((differentiable_id.mul (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const 1

theorem analyticOnNhd_xi : AnalyticOnNhd ℂ xi Set.univ :=
  differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ

theorem analyticAt_xi (s : ℂ) : AnalyticAt ℂ xi s := analyticOnNhd_xi s (Set.mem_univ s)

theorem continuous_xi : Continuous xi := differentiable_xi.continuous

@[simp] theorem xi_zero : xi 0 = 1 := by simp [xi]

@[simp] theorem xi_one : xi 1 = 1 := by simp [xi]

/-- The functional equation `xi (1 - s) = xi s`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Off `0` and `1` and the trivial zeros of `Γ(s/2)`, `xi s = s (s - 1) Γℝ(s) ζ(s)`. -/
theorem xi_eq_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    xi s = s * (s - 1) * (Gammaℝ s * ζ s) := by
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold xi
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

/-- `xi` is real on the real axis and nonvanishing off the strip: conjugation symmetry. -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  by_cases hs0 : s = 0
  · subst hs0; simp
  by_cases hs1 : s = 1
  · subst hs1; simp
  have hc0 : conj s ≠ 0 := by simpa using hs0
  have hc1 : conj s ≠ 1 := fun h => hs1 (by simpa using congrArg conj h)
  have key : ∀ {z : ℂ}, z ≠ 0 → z ≠ 1 →
      xi z = z * (z - 1) * (completedRiemannZeta z + 1 / z + 1 / (1 - z)) + 1 := by
    intro z hz0 hz1
    unfold xi
    rw [completedRiemannZeta_eq]
    ring
  rw [key hc0 hc1, key hs0 hs1, completedRiemannZeta_conj]
  simp only [map_add, map_mul, map_sub, map_one, map_div₀]

/-- `xi s ≠ 0` for `Re s ≥ 1`. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; simp
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at h; norm_num at h
  rw [xi_eq_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
    (mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith)) (riemannZeta_ne_zero_of_one_le_re h))

/-- `xi s ≠ 0` for `Re s ≤ 0`. -/
theorem xi_ne_zero_of_re_nonpos {s : ℂ} (h : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp; linarith)

/-- In the open strip, `xi` vanishes exactly where `ζ` does. -/
theorem xi_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : xi s = 0 ↔ ζ s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hG := Gammaℝ_ne_zero_of_re_pos h0
  rw [xi_eq_mul hs0 hs1 hG]
  simp [hs0, sub_ne_zero.mpr hs1, hG]

/-- A zero of `xi` lies in the open strip. -/
theorem re_pos_lt_one_of_xi_eq_zero {s : ℂ} (h : xi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hc; exact xi_ne_zero_of_re_nonpos (not_lt.mp hc) h
  · by_contra hc; exact xi_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- `Γℝ` is analytic at points of positive real part. -/
theorem analyticAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hG : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) z := by
      apply (differentiableAt_Gamma _ ?_).comp z (differentiableAt_id.div_const 2)
      intro m hm
      have := congrArg re hm
      simp at this
      have hz' : 0 < z.re := hz
      linarith [this, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hp : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) z :=
      (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    exact (hp.mul hG).differentiableWithinAt
  exact (hd.analyticOnNhd hU) s hs

/-- In the open strip, `xi` and `ζ` have the same order at every point. -/
theorem analyticOrderNatAt_xi {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ := by
  set g : ℂ → ℂ := fun s => s * (s - 1) * Gammaℝ s with hg
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const continuous_re).and (isOpen_lt continuous_re continuous_const)
  have hev : xi =ᶠ[nhds ρ] g * ζ := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with s hs
    simp only [Pi.mul_apply, hg]
    rw [xi_eq_mul (fun h => by rw [h] at hs; simp at hs) (fun h => by rw [h] at hs; simp at hs)
      (Gammaℝ_ne_zero_of_re_pos hs.1)]
    ring
  have hgA : AnalyticAt ℂ g ρ :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (analyticAt_Gammaℝ_of_re_pos h0))
  have hg0 : g ρ ≠ 0 := by
    simp only [hg]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (Gammaℝ_ne_zero_of_re_pos h0)
    · intro h; rw [h] at h0; simp at h0
    · intro h; rw [sub_eq_zero] at h; rw [h] at h1; simp at h1
  have hζ : AnalyticAt ℂ ζ ρ := analyticAt_riemannZeta (fun h => by rw [h] at h1; simp at h1)
  have : analyticOrderAt xi ρ = analyticOrderAt ζ ρ := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hgA hζ,
      analyticOrderAt_eq_zero.mpr (Or.inr hg0), zero_add]
  simp only [analyticOrderNatAt, this]

/-- `Γℝ` is a positive real on the positive real axis. -/
theorem Gammaℝ_ofReal_pos {σ : ℝ} (hσ : 0 < σ) :
    Gammaℝ (σ : ℂ) = ((π ^ (-σ / 2) * Real.Gamma (σ / 2) : ℝ) : ℂ) ∧
      0 < π ^ (-σ / 2) * Real.Gamma (σ / 2) := by
  refine ⟨?_, mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))⟩
  rw [Gammaℝ_def, ofReal_mul, ofReal_cpow Real.pi_pos.le, ← Gamma_ofReal]
  push_cast
  ring_nf

/-- `xi` is a positive real on the real axis. -/
theorem xi_ofReal_pos (σ : ℝ) : xi σ = ((xi σ).re : ℂ) ∧ 0 < (xi σ).re := by
  -- reduce to `σ ≥ 1/2` by the functional equation
  suffices h : ∀ σ : ℝ, 1 / 2 ≤ σ → xi σ = ((xi σ).re : ℂ) ∧ 0 < (xi σ).re by
    rcases le_or_gt (1 / 2) σ with hσ | hσ
    · exact h σ hσ
    · have := h (1 - σ) (by linarith)
      rwa [ofReal_sub, ofReal_one, xi_one_sub] at this
  intro σ hσ
  by_cases h1 : σ = 1
  · subst h1; simp
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith [hσ])
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1
  have hG := Gammaℝ_ofReal_pos (show 0 < σ by linarith)
  have hGne : Gammaℝ (σ : ℂ) ≠ 0 := by rw [hG.1]; exact_mod_cast hG.2.ne'
  rw [xi_eq_mul hs0 hs1 hGne, hG.1]
  -- `ζ σ` is real with sign opposite to `σ (σ - 1)`
  have hζ : ζ σ = ((ζ σ).re : ℂ) ∧ 0 < σ * (σ - 1) * (ζ σ).re := by
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have h := Complex.lt_def.mp (TauCeti.riemannZeta_lt_zero (σ := σ) (by linarith) hlt)
      simp only [zero_re, zero_im] at h
      refine ⟨(Complex.ext_iff.mpr ⟨by simp, by simp [h.2]⟩), ?_⟩
      have : σ * (σ - 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith [h.1]
    · refine ⟨(Complex.ext_iff.mpr ⟨by simp, by simp [riemannZeta_im_eq_zero_of_one_lt hgt]⟩), ?_⟩
      have := riemannZeta_re_pos_of_one_lt hgt
      have : 0 < σ * (σ - 1) := mul_pos (by linarith) (by linarith)
      positivity
  rw [hζ.1]
  have e : (σ : ℂ) * (σ - 1) * (((π ^ (-σ / 2) * Real.Gamma (σ / 2) : ℝ) : ℂ) * ((ζ σ).re : ℂ)) =
      ((σ * (σ - 1) * (π ^ (-σ / 2) * Real.Gamma (σ / 2)) * (ζ σ).re : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, ofReal_re]
  refine ⟨rfl, ?_⟩
  have := hG.2
  nlinarith [hζ.2, hG.2]

/-- `xi σ ≠ 0` on the real axis. -/
theorem xi_ofReal_ne_zero (σ : ℝ) : xi σ ≠ 0 := by
  intro h
  have := (xi_ofReal_pos σ).2
  rw [h] at this
  simp at this

/-- The zeros of `xi` at a given height `t`, in terms of `ζ`: if `ζ` has no zero on
`[1/2, 1) + it`, `xi` has no zero on the whole horizontal line at height `t ≠ 0`. -/
theorem xi_ne_zero_of_notOrdinate {t : ℝ}
    (hord : ∀ σ ∈ Set.Ico (1 / 2 : ℝ) 1, ζ (σ + t * I) ≠ 0) (σ : ℝ) : xi (σ + t * I) ≠ 0 := by
  intro h
  obtain ⟨h0, h1⟩ := re_pos_lt_one_of_xi_eq_zero h
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero] at h0 h1
  have hz : ζ (σ + t * I) = 0 := (xi_eq_zero_iff (by simpa using h0) (by simpa using h1)).mp h
  rcases le_or_gt (1 / 2) σ with hσ | hσ
  · exact hord σ ⟨hσ, h1⟩ hz
  · -- reflect: `ζ (1 - σ - it) = 0`, conjugate: `ζ (1 - σ + it) = 0`
    have h2 := zeta_one_sub_eq_zero (ρ := σ + t * I) (by simpa using h0) (by simpa using h1) hz
    have h3 : ζ ((1 - σ : ℝ) + t * I) = 0 := by
      have hc : ((1 - σ : ℝ) + t * I : ℂ) = conj (1 - (σ + t * I)) := by
        apply Complex.ext <;> simp
      rw [hc, riemannZeta_conj, h2, map_zero]
    exact hord (1 - σ) ⟨by linarith, by linarith⟩ h3

end SchoenfeldS1

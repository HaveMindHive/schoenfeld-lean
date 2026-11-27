/-
Schoenfeld S1, part C (WORK IN PROGRESS, contains `sorry`): the Riemann-von Mangoldt identity
`N(T) = θ(T)/π + 1 + S(T)` and everything downstream of it. Not delivered.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldS1.B
import SchoenfeldS1.D3
import SchoenfeldS1.G
import SchoenfeldS1.Z

/-!
# Target (C) and the assembly

(D) is delivered in `SchoenfeldS1.D3` (`abs_riemannZetaS_le_backlund`, `abs_riemannZetaS_le`).
The only `sorry` left is `NT_eq_rsTheta_add`; everything after it compiles.
-/

namespace SchoenfeldS1

open Complex Real Set Filter Topology
open TauCeti.LFunctions (riemannZetaS)
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt)

local notation "ζ" => riemannZeta

/-- **(C), target.** The Riemann-von Mangoldt identity: for `T ≥ 14` not an ordinate,
`N(T) = θ(T)/π + 1 + S(T)` with `rsTheta` of `SchoenfeldS1.B` (the continuous branch,
`rsTheta 0 = 0`). -/
theorem NT_eq_rsTheta_add {T : ℝ} (hT : 14 ≤ T) (hord : NotOrdinate T) :
    (NT T : ℝ) = rsTheta T / π + 1 + riemannZetaS T := by
  sorry

/-- `Mt T = rsThetaMain T/π + 1`. -/
lemma Mt_eq_rsThetaMain {T : ℝ} (hT : 0 < T) : Mt T = rsThetaMain T / π + 1 := by
  unfold Mt rsThetaMain
  have h : Real.log (T / (2 * π * Real.exp 1)) = Real.log (T / (2 * π)) - 1 := by
    rw [show T / (2 * π * Real.exp 1) = T / (2 * π) / Real.exp 1 by ring,
      Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  rw [h]
  field_simp
  ring

/-- From (B), (C), (D): `|N(T) - Mt T| ≤ RtB T` for `T ≥ 14` not an ordinate. -/
theorem abs_NT_sub_Mt_le {T : ℝ} (hT : 14 ≤ T) (hord : NotOrdinate T) :
    |(NT T : ℝ) - Mt T| ≤ RtB T := by
  rw [NT_eq_rsTheta_add hT hord, Mt_eq_rsThetaMain (by linarith)]
  have h1 := abs_rsTheta_sub_main_le_of_fourteen_le hT
  have h2 := abs_riemannZetaS_le hT hord
  have hpi := Real.pi_gt_three
  have e : rsTheta T / π + 1 + riemannZetaS T - (rsThetaMain T / π + 1) =
      (rsTheta T - rsThetaMain T) / π + riemannZetaS T := by ring
  rw [e]
  unfold RtB
  calc |(rsTheta T - rsThetaMain T) / π + riemannZetaS T|
      ≤ |(rsTheta T - rsThetaMain T) / π| + |riemannZetaS T| := abs_add_le _ _
    _ ≤ (11 / 224) / π + (4.5 * Real.log T + 17.08) := by
        gcongr
        rw [abs_div, abs_of_pos Real.pi_pos]
        exact div_le_div_of_nonneg_right h1 Real.pi_pos.le
    _ ≤ 4.5 * Real.log T + 17.1 := by
        have : (11 / 224 : ℝ) / π ≤ 0.02 := by
          rw [div_le_iff₀ Real.pi_pos]; linarith
        linarith

/-- `Mt + RtB` and `Mt - RtB` are continuous at every `T > 0`. -/
lemma continuousAt_Mt {T : ℝ} (hT : 0 < T) : ContinuousAt Mt T := by
  unfold Mt
  have h1 : ContinuousAt (fun T : ℝ => Real.log (T / (2 * π * Real.exp 1))) T :=
    (Real.continuousAt_log (by positivity)).comp (by fun_prop)
  exact ((continuousAt_id.div_const _).mul h1).add continuousAt_const

lemma continuousAt_RtB {T : ℝ} (hT : 0 < T) : ContinuousAt RtB T := by
  unfold RtB
  exact ((Real.continuousAt_log hT.ne').const_mul _).add continuousAt_const

/-- A zero of `ζ` at height `t` in the strip lies in the band `(a, b]` when `a < t ≤ b`. -/
lemma mem_zerosBandF_of_zero {a b σ t : ℝ} (hz : ζ (σ + t * I) = 0) (h0 : 0 < σ) (h1 : σ < 1)
    (ha : a < t) (hb : t ≤ b) : (σ + t * I : ℂ) ∈ zerosBandF a b := by
  rw [mem_zerosBandF]
  refine ⟨hz, ?_, ?_, ?_, ?_⟩ <;> simp [h0, h1, ha, hb]

/-- Zeros of the strip at height `t` with `0 < Re < 1` are excluded by `NotOrdinate` and the
reflection `ρ ↦ 1 - ρ` plus conjugation; conversely a zero at height `t` makes `t` an ordinate. -/
lemma notOrdinate_of_no_zero {t : ℝ} (h : ∀ σ : ℝ, 0 < σ → σ < 1 → ζ (σ + t * I) ≠ 0) :
    NotOrdinate t := fun σ hσ => h σ (by linarith [hσ.1]) hσ.2

/-- **(U')** for all `T ≥ 14`: right limits through non-ordinates. -/
theorem NT_le_Mt_add_RtB {T : ℝ} (hT : 14 ≤ T) : (NT T : ℝ) ≤ Mt T + RtB T := by
  have hcont : Tendsto (fun T' => Mt T' + RtB T') (𝓝[>] T) (𝓝 (Mt T + RtB T)) :=
    (((continuousAt_Mt (by linarith)).add (continuousAt_RtB (by linarith))).tendsto).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  have h1 : ∀ᶠ T' in 𝓝[>] T, T' ∈ Ioo T (T + 1) := Ioo_mem_nhdsGT (by linarith)
  have h2 : ∀ᶠ T' in 𝓝[>] T, ∀ ρ ∈ zerosBandF T (T + 1), T' < ρ.im := by
    rw [Filter.eventually_all_finset]
    intro ρ hρ
    exact (eventually_lt_nhds (mem_zerosBandF.mp hρ).2.2.2.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with T' hT' hρ
  have hord : NotOrdinate T' := notOrdinate_of_no_zero fun σ h0 h1 hz =>
    lt_irrefl T' (by simpa using hρ _ (mem_zerosBandF_of_zero hz h0 h1 hT'.1 hT'.2.le))
  have hNT : NT T' = NT T := by
    unfold NT Nband
    congr 1
    ext ρ
    simp only [mem_zerosBandF]
    constructor
    · rintro ⟨hz, h0, h1, h0i, hi⟩
      refine ⟨hz, h0, h1, h0i, ?_⟩
      by_contra hcon
      push_neg at hcon
      have := hρ ρ (mem_zerosBandF.mpr ⟨hz, h0, h1, hcon, hi.trans hT'.2.le⟩)
      linarith
    · rintro ⟨hz, h0, h1, h0i, hi⟩
      exact ⟨hz, h0, h1, h0i, hi.trans hT'.1.le⟩
  have := abs_NT_sub_Mt_le (T := T') (by linarith [hT'.1]) hord
  rw [abs_le] at this
  rw [← hNT]
  linarith [this.2]

/-- **(L')** for all `T ≥ 1000`: left limits through non-ordinates, `NT` monotone. -/
theorem Mt_sub_RtB_le_NT {T : ℝ} (hT : 1000 ≤ T) : Mt T - RtB T ≤ NT T := by
  have hcont : Tendsto (fun T' => Mt T' - RtB T') (𝓝[<] T) (𝓝 (Mt T - RtB T)) :=
    (((continuousAt_Mt (by linarith)).sub (continuousAt_RtB (by linarith))).tendsto).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  have h1 : ∀ᶠ T' in 𝓝[<] T, T' ∈ Ioo (T - 1) T := Ioo_mem_nhdsLT (by linarith)
  have h2 : ∀ᶠ T' in 𝓝[<] T, ∀ ρ ∈ zerosBandF (T - 1) T, ρ.im < T' ∨ ρ.im = T := by
    rw [Filter.eventually_all_finset]
    intro ρ hρ
    rcases (mem_zerosBandF.mp hρ).2.2.2.2.lt_or_eq with hlt | heq
    · exact ((eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => Or.inl h
    · exact Filter.Eventually.of_forall fun _ => Or.inr heq
  filter_upwards [h1, h2] with T' hT' hρ
  have hord : NotOrdinate T' := notOrdinate_of_no_zero fun σ h0 h1 hz => by
    have := hρ _ (mem_zerosBandF_of_zero hz h0 h1 hT'.1 hT'.2.le)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, ofReal_im, mul_im, zero_add] at this
    rcases this with h | h
    · exact lt_irrefl _ h
    · exact hT'.2.ne h
  have hmono : NT T' ≤ NT T := by
    have := Nband_add (T := T') (t := T) (by linarith [hT'.1]) hT'.2.le
    unfold NT
    rw [this]
    exact Nat.le_add_right _ _
  have := abs_NT_sub_Mt_le (T := T') (by linarith [hT'.1]) hord
  rw [abs_le] at this
  have hmono' : (NT T' : ℝ) ≤ NT T := by exact_mod_cast hmono
  linarith [this.1]

/-- Schoenfeld's bound for `x ≥ 10^15` from `N(14) = 0` alone. -/
theorem schoenfeld_psi_large_of_Z (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_psi_large_of_NTB (fun _ hT => NT_le_Mt_add_RtB hT) (fun _ hT => Mt_sub_RtB_le_NT hT) h14

/-- **Schoenfeld's bound, unconditional** (modulo the `sorry` in `NT_eq_rsTheta_add`):
`|ψ(x) - x| ≤ √x log² x/(8π)` for every `x ≥ 10^15`. -/
theorem schoenfeld_psi :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_psi_large_of_Z NT_fourteen_eq_zero

/-- The `θ` version. -/
theorem schoenfeld_theta :
    ∀ x ≥ (10 : ℝ) ^ 15, |Chebyshev.theta x - x| ≤ √x * Real.log x ^ 2 / (8 * π) :=
  schoenfeld_theta_large_of_NTB (fun _ hT => NT_le_Mt_add_RtB hT) (fun _ hT => Mt_sub_RtB_le_NT hT)
    NT_fourteen_eq_zero

end SchoenfeldS1

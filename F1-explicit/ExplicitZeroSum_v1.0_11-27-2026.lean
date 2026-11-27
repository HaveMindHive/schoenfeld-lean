import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer

import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# An explicit bound on `∑ m(ρ)/|ρ|` over the zeros of `ζ` (11-27-2026)

Same environment as `WallsMeetRHVonKoch_v1.0_11-27-2026.lean` (the locally built community proof
of RH, Mathlib `31ce06ea`, Tau Ceti pinned). Given a count constant `Cc` for the zeros in the
closed discs of radius `29/16` about `2 + i t`, the sum of `m(ρ)/|ρ|` over zeros with
`1/4 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is at most `32 Cc log²(T + 2)`.

By the proved RH every such zero has `Re ρ = 1/2`; the zeros with `⌊σ Im ρ⌋ = k` then lie in the
disc of radius `29/16` about `2 + iσ(k + 1/2)`, since `(3/2)² + (1/2)² = 10/4 ≤ (29/16)²`.
-/

open Complex

namespace WallsMeetRHExplicit

/-- From the proved `riemannHypothesis` (copied from the von Koch file): a zero of `ζ` in the
strip `0 < Re ρ < 1` has `Re ρ = 1/2`. -/
theorem zsum_re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

theorem zsum_one_le_log_add_two {T : ℝ} (hT : 1 ≤ T) : 1 ≤ Real.log (T + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- The half-plane case, `σ = ±1`. -/
theorem zsum_half {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 1 ≤ T) (P : Finset ℂ)
    (hP : ∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ 0 ≤ σ * z.im ∧ σ * z.im ≤ T) :
    ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤
      8 * Cc * Real.log (T + 2) * (1 + Real.log (T + 1)) := by
  classical
  set m : ℂ → ℝ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set N := ⌊T⌋₊
  have hmaps : ∀ z ∈ P, ⌊σ * z.im⌋₊ ∈ Finset.range (N + 1) := fun z hz ↦ by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hP z hz).2.2.2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlogT : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hfib : ∀ k ∈ Finset.range (N + 1),
      ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖ ≤
        8 * Cc * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ := fun k hk ↦ by
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    -- the fibre lies in the disc of radius `29/16` about `2 + iσ(k + 1/2)`
    have hsub : P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k) ⊆
        TauCeti.riemannZetaZerosClosedBall (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I) (29 / 16) := by
      intro z hz
      obtain ⟨hzP, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3, h4⟩ := hP z hzP
      have hre : z.re = 1 / 2 := zsum_re_eq_half_of_zero (by linarith)
        (TauCeti.re_lt_one_of_riemannZeta_eq_zero hζ) hζ
      have hfl := Nat.floor_le h3
      have hfl' := Nat.lt_floor_add_one (σ * z.im)
      rw [hzk] at hfl hfl'
      refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, hζ⟩
      set w := z - (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I)
      have hwre : w.re = z.re - 2 := by simp [w]
      have hwim : w.im = σ * (σ * z.im - (k + 1 / 2)) := by
        simp only [w, sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
        norm_num
        linear_combination (-z.im) * hσσ
      have hsq : ‖w‖ ^ 2 ≤ (29 / 16) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim, hre]
        have : (σ * (σ * z.im - (k + 1 / 2))) * (σ * (σ * z.im - (k + 1 / 2))) =
            (σ * z.im - (k + 1 / 2)) ^ 2 := by
          linear_combination (σ * z.im - (k + 1 / 2)) ^ 2 * hσσ
        rw [this]
        nlinarith
      nlinarith [norm_nonneg w]
    have hnorm : ∀ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), 1 / ‖z‖ ≤ 4 * ((k : ℝ) + 1)⁻¹ :=
      fun z hz ↦ by
      obtain ⟨hzP, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3, h4⟩ := hP z hzP
      have hfl := Nat.floor_le h3
      rw [hzk] at hfl
      have hre : 1 / 4 ≤ ‖z‖ := h1.trans ((le_abs_self _).trans (abs_re_le_norm z))
      have him : (k : ℝ) ≤ ‖z‖ := by
        calc (k : ℝ) ≤ σ * z.im := hfl
          _ ≤ |σ * z.im| := le_abs_self _
          _ = |z.im| := by rw [abs_mul, hσabs, one_mul]
          _ ≤ ‖z‖ := abs_im_le_norm z
      have hz0 : 0 < ‖z‖ := by linarith
      rw [div_le_iff₀ hz0]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num; linarith
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        rw [show 4 * ((k : ℝ) + 1)⁻¹ * ‖z‖ = 4 * ‖z‖ / (k + 1) by ring, le_div_iff₀ (by linarith)]
        nlinarith
    have hcount : ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z ≤
        2 * Cc * Real.log (T + 2) := by
      have h := hCc (σ * (k + 1 / 2))
      rw [abs_mul, hσabs, one_mul, abs_of_nonneg (by positivity)] at h
      have hk' : (k : ℝ) ≤ T := by
        have : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact this.trans (Nat.floor_le (by linarith))
      have hlog : Real.log ((k : ℝ) + 1 / 2 + 2) ≤ 2 * Real.log (T + 2) := by
        rw [show (2 : ℝ) * Real.log (T + 2) = ((2 : ℕ) : ℝ) * Real.log (T + 2) by norm_num,
          ← Real.log_pow]
        exact Real.log_le_log (by positivity) (by nlinarith)
      calc ∑ z ∈ P.filter (fun z ↦ ⌊σ * z.im⌋₊ = k), m z
          ≤ ∑ z ∈ TauCeti.riemannZetaZerosClosedBall
              (2 + ((σ * (k + 1 / 2) : ℝ) : ℂ) * I) (29 / 16), m z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
        _ ≤ Cc * Real.log ((k : ℝ) + 1 / 2 + 2) := h
        _ ≤ Cc * (2 * Real.log (T + 2)) := by gcongr
        _ = 2 * Cc * Real.log (T + 2) := by ring
    calc ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖
        ≤ ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z * (4 * ((k : ℝ) + 1)⁻¹) := by
          refine Finset.sum_le_sum fun z hz ↦ ?_
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (hnorm z hz) (by positivity)
      _ = (∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z) * (4 * ((k : ℝ) + 1)⁻¹) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * Cc * Real.log (T + 2) * (4 * ((k : ℝ) + 1)⁻¹) := by gcongr
      _ = _ := by ring
  have hharm : ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ ≤ 1 + Real.log (T + 1) := by
    have h := harmonic_le_one_add_log (N + 1)
    have hcast : ((harmonic (N + 1) : ℚ) : ℝ) = ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
      simp only [harmonic]
      push_cast
      rfl
    rw [hcast] at h
    refine h.trans ?_
    have : ((N + 1 : ℕ) : ℝ) ≤ T + 1 := by
      push_cast; linarith [Nat.floor_le (show (0 : ℝ) ≤ T by linarith)]
    linarith [Real.log_le_log (by positivity) this]
  calc ∑ k ∈ Finset.range (N + 1), ∑ z ∈ P with ⌊σ * z.im⌋₊ = k, m z / ‖z‖
      ≤ ∑ k ∈ Finset.range (N + 1), 8 * Cc * Real.log (T + 2) * ((k : ℝ) + 1)⁻¹ :=
        Finset.sum_le_sum hfib
    _ = 8 * Cc * Real.log (T + 2) * ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 8 * Cc * Real.log (T + 2) * (1 + Real.log (T + 1)) := by gcongr

/-- **`∑ m(ρ)/|ρ| ≤ 32 Cc log²(T + 2)`** over any finite set of zeros of `ζ` with
`1/4 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`, `T ≥ 1`, given the count `Cc log(|t| + 2)` on the discs of
radius `29/16` about `2 + i t`. -/
theorem sum_order_div_norm_le_of {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2)) :
    ∀ T : ℝ, 1 ≤ T → ∀ P : Finset ℂ,
      (∀ z ∈ P, 1 / 4 ≤ z.re ∧ z.re ≤ 1 ∧ riemannZeta z = 0 ∧ |z.im| ≤ T) →
      ∑ z ∈ P, ((analyticOrderAt riemannZeta z).toNat : ℝ) / ‖z‖ ≤
        32 * Cc * Real.log (T + 2) ^ 2 := by
  classical
  intro T hT P hP
  have hup := zsum_half hCc0 hCc (Or.inl rfl) hT (P.filter fun z ↦ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by simpa using h0, by rw [one_mul]; exact (le_abs_self _).trans h3⟩
  have hdn := zsum_half hCc0 hCc (Or.inr rfl) hT (P.filter fun z ↦ ¬ 0 ≤ z.im)
    fun z hz ↦ by
      obtain ⟨hzP, h0⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2, hζ, h3⟩ := hP z hzP
      exact ⟨h1, h2, hζ, by rw [neg_one_mul]; linarith [not_le.mp h0], by
        rw [neg_one_mul]; exact (neg_le_abs _).trans h3⟩
  rw [← Finset.sum_filter_add_sum_filter_not P fun z ↦ 0 ≤ z.im]
  have hl1 : 1 ≤ Real.log (T + 2) := zsum_one_le_log_add_two hT
  have hl2 : Real.log (T + 1) ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
  nlinarith [mul_nonneg hCc0 (sub_nonneg.2 hl1), mul_nonneg hCc0 (sub_nonneg.2 hl2),
    mul_nonneg (mul_nonneg hCc0 (sub_nonneg.2 hl1)) (sub_nonneg.2 hl2)]

end WallsMeetRHExplicit

#print axioms WallsMeetRHExplicit.sum_order_div_norm_le_of

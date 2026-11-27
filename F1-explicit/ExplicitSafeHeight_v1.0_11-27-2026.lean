import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer

import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# An explicit safe height for `ζ′/ζ` (11-27-2026)

`riemannZeta_safe_height_of`: Tau Ceti's `riemannZeta_safe_height` with its two existential
inputs (the window constant `Cw` and the zero count constant `Cc`) taken as hypotheses, and the
safe height constant given in closed form, `2 |Cw| + 288 Cc² + 24 |Cc| + 1`.

Two changes from Tau Ceti: the window form is assumed only for `1/4 ≤ Re s ≤ 2`, and the zero
count is for discs of radius `29/16` about `2 + i t`. The proved RH puts every window zero on
`Re = 1/2`, so six such discs cover the window zeros about the points `σ ± i T′`, `T′ ∈ [T, T + 1]`.

The proofs are adapted from Tau Ceti Window.lean, Apache 2.0, The Tau Ceti contributors.
-/

open Complex

namespace WallsMeetRHExplicit

/-- From the proved `riemannHypothesis`: a zero of `ζ` in the strip `0 < Re ρ < 1` has
`Re ρ = 1/2`. -/
theorem safe_re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): a zero outside the window about `s` is at
distance at least `1` from `s`, when `1/4 ≤ Re s`. -/
theorem safe_one_le_norm_sub_of_riemannZeta_eq_zero {s ρ : ℂ} (hs : 1 / 4 ≤ s.re)
    (hρ : riemannZeta ρ = 0) (hw : ¬(0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - s.im| ≤ 1)) :
    1 ≤ ‖s - ρ‖ := by
  rcases le_or_gt ρ.re 0 with h0 | h0
  · obtain ⟨n, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h0).mp hρ
    have hre : (s - -2 * ((n : ℂ) + 1)).re = s.re + 2 * (n + 1) := by simp
    refine le_trans ?_ ((le_abs_self _).trans (abs_re_le_norm _))
    rw [hre]
    linarith [n.cast_nonneg (α := ℝ)]
  rcases lt_or_ge ρ.re 1 with h1 | h1
  · have : 1 < |ρ.im - s.im| := by
      by_contra h
      exact hw ⟨h0, h1, not_lt.mp h⟩
    rw [abs_sub_comm] at this
    exact this.le.trans (by simpa using abs_im_le_norm (s - ρ))
  · exact absurd hρ (riemannZeta_ne_zero_of_one_le_re h1)

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): the window sum over a finite set `Z`
containing the window zeros, all at distance `≥ δ > 0` from `s`, is at most `∑_Z m / δ`. -/
theorem safe_norm_finsum_window_le {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    ‖∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
      (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ := by
  classical
  rw [TauCeti.finsum_window_eq_sum_filter hZ
    fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z), Finset.sum_div]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z hz ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity))
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (by positivity) hδ (hsep z (Finset.mem_filter.mp hz).1)

/-- Adapted from Tau Ceti Window.lean (Apache 2.0): the estimate at a separated point. -/
theorem safe_riemannZeta_ne_zero_and_norm_logDeriv_le {C : ℝ}
    (hC : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s.im| + 2))
    {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ) (hs₁ : 1 / 4 ≤ s.re) (hs₂ : s.re ≤ 2)
    (hsim : 2 ≤ |s.im|)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    riemannZeta s ≠ 0 ∧ ‖deriv riemannZeta s / riemannZeta s‖ ≤
      C * Real.log (|s.im| + 2) + (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ + 1 := by
  have hζ : riemannZeta s ≠ 0 := fun hζ ↦ by
    by_cases hw : 0 < s.re ∧ s.re < 1 ∧ |s.im - s.im| ≤ 1
    · have := hsep s (hZ s hw.1 hw.2.1 hw.2.2 hζ)
      rw [sub_self, norm_zero] at this
      linarith
    · have := safe_one_le_norm_sub_of_riemannZeta_eq_zero hs₁ hζ hw
      rw [sub_self, norm_zero] at this
      linarith
  refine ⟨hζ, ?_⟩
  have hs1 : 2 ≤ ‖s - 1‖ := hsim.trans (by simpa using abs_im_le_norm (s - 1))
  have hpole : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hs1' : s ≠ 1 := fun h ↦ by norm_num [h] at hs1
  set W := ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
    ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)
  have hsplit : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - W) + W - 1 / (s - 1) := by ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (hC s hs₁ hs₂ hs1' hζ) (safe_norm_finsum_window_le hδ hZ hsep))) hpole)

/-- A zero `ρ` with `Re ρ = 1/2` and `|Im ρ - t| ≤ 1/2` lies in the closed disc of radius
`29/16` about `2 + i t` (distance `≤ √10 / 2 < 29/16`). -/
theorem safe_mem_ball {ρ : ℂ} {t : ℝ} (hre : ρ.re = 1 / 2) (him : |ρ.im - t| ≤ 1 / 2)
    (hζ : riemannZeta ρ = 0) :
    ρ ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16) := by
  refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, hζ⟩
  have h1 : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have h2 : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ 10 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2, hre]
    have := abs_le.mp him
    nlinarith
  nlinarith [norm_nonneg (ρ - (2 + t * I))]

/-- The disc of radius `29/16` about `2 + i t`. -/
noncomputable abbrev safe_B (t : ℝ) : Finset ℂ :=
  TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16)

/-- The six discs covering the window zeros at heights `±T′`, `T′ ∈ [T, T + 1]`. -/
noncomputable abbrev safe_Z (T : ℝ) : Finset ℂ :=
  safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2)) ∪ safe_B (-(T + 1 / 2)) ∪ safe_B (-(T + 3 / 2))

/-- Every window zero about `s` with `T ≤ |Im s| ≤ T + 1` lies in `safe_Z T`. -/
theorem safe_mem_Z {T : ℝ} {s ρ : ℂ} (hT : T ≤ |s.im|) (hT' : |s.im| ≤ T + 1)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hw : |ρ.im - s.im| ≤ 1) (hζ : riemannZeta ρ = 0) :
    ρ ∈ safe_Z T := by
  have hre := safe_re_eq_half_of_zero h0 h1 hζ
  have him : |(|ρ.im| - T)| ≤ 2 ∧ |(|ρ.im| - (T + 1))| ≤ 2 := by
    have := (abs_abs_sub_abs_le_abs_sub ρ.im s.im).trans hw
    rw [abs_le] at this
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have ha := abs_le.mp him.1
  have hb := abs_le.mp him.2
  simp only [safe_Z, Finset.mem_union]
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at ha hb
    rcases le_or_gt ρ.im T with h2 | h2
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    rcases le_or_gt ρ.im (T + 1) with h3 | h3
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
  · rw [abs_of_neg h] at ha hb
    rcases le_or_gt (-ρ.im) T with h2 | h2
    · exact Or.inl <| Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    rcases le_or_gt (-ρ.im) (T + 1) with h3 | h3
    · exact Or.inl <| Or.inr <|
        safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ
    · exact Or.inr <| safe_mem_ball hre (abs_le.mpr ⟨by linarith, by linarith⟩) hζ

/-- A sum of the nonnegative weights `m` over a union is at most the sum of the two sums. -/
theorem safe_sum_union_le (A B : Finset ℂ) :
    ∑ z ∈ A ∪ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ (∑ z ∈ A, ((analyticOrderAt riemannZeta z).toNat : ℝ)) + ∑ z ∈ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  classical
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B)
    (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ))
  have h0 : 0 ≤ ∑ z ∈ A ∩ B, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by positivity
  linarith

/-- The zeros of `safe_Z T`, counted with order, number at most `12 |Cc| log (T + 2)`. -/
theorem safe_sum_Z_le {Cc : ℝ}
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2))
    {T : ℝ} (hT : 2 ≤ T) :
    ∑ z ∈ safe_Z T, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 12 * |Cc| * Real.log (T + 2) := by
  have hdisc (t : ℝ) (ht : |t| ≤ T + 3 / 2) :
      ∑ z ∈ safe_B t, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 2 * |Cc| * Real.log (T + 2) := by
    have hlog : Real.log (|t| + 2) ≤ 2 * Real.log (T + 2) :=
      Real.log_add_two_le_two_mul_log_add_two (by linarith) (abs_nonneg _)
        (by linarith)
    have hl0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    calc ∑ z ∈ safe_B t, ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2) := hCc t
      _ ≤ |Cc| * Real.log (|t| + 2) := mul_le_mul_of_nonneg_right (le_abs_self Cc) hl0
      _ ≤ |Cc| * (2 * Real.log (T + 2)) := mul_le_mul_of_nonneg_left hlog (abs_nonneg Cc)
      _ = _ := by ring
  have a1 := hdisc (T - 1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a2 := hdisc (T + 1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a3 := hdisc (T + 3 / 2) (by rw [abs_le]; constructor <;> linarith)
  have a4 := hdisc (-(T - 1 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have a5 := hdisc (-(T + 1 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have a6 := hdisc (-(T + 3 / 2)) (by rw [abs_le]; constructor <;> linarith)
  have u5 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2)) ∪ safe_B (-(T + 1 / 2))) (safe_B (-(T + 3 / 2)))
  have u4 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2) ∪
    safe_B (-(T - 1 / 2))) (safe_B (-(T + 1 / 2)))
  have u3 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2) ∪ safe_B (T + 3 / 2))
    (safe_B (-(T - 1 / 2)))
  have u2 := safe_sum_union_le (safe_B (T - 1 / 2) ∪ safe_B (T + 1 / 2)) (safe_B (T + 3 / 2))
  have u1 := safe_sum_union_le (safe_B (T - 1 / 2)) (safe_B (T + 1 / 2))
  simp only [safe_Z]
  linarith

/-- Every point of a finite set of zeros has order `≥ 1`: adapted from Tau Ceti Window.lean
(Apache 2.0). -/
theorem safe_card_image_abs_im_le_sum {Z : Finset ℂ} (hZ : ∀ z ∈ Z, riemannZeta z = 0) :
    ((Z.image fun z ↦ |z.im|).card : ℝ) ≤ ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun z hz ↦ by
    exact_mod_cast TauCeti.one_le_toNat_analyticOrderAt_riemannZeta (hZ z hz)

/-- The final arithmetic, adapted from Tau Ceti Window.lean (Apache 2.0): if `1 ≤ L`,
`0 ≤ l ≤ 2 L` and `0 ≤ K ≤ 12 |C'| L`, then
`C l + 2 K (K + 1) + 1 ≤ (2 |C| + 288 C'² + 24 |C'| + 1) L²`. -/
theorem safe_final_arith {C C' K L l : ℝ} (hL : 1 ≤ L) (hl : 0 ≤ l)
    (hlL : l ≤ 2 * L) (hK0 : 0 ≤ K) (hK : K ≤ 12 * |C'| * L) :
    C * l + 2 * K * (K + 1) + 1 ≤ (2 * |C| + 288 * C' ^ 2 + 24 * |C'| + 1) * L ^ 2 := by
  have hC : C * l ≤ |C| * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hl).trans
      (mul_le_mul_of_nonneg_left hlL (abs_nonneg C))
  have hL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith [abs_nonneg C', abs_nonneg C, sq_abs C',
    mul_le_mul hK hK hK0 (by nlinarith [abs_nonneg C']),
    mul_le_mul_of_nonneg_left hL2 (abs_nonneg C), mul_le_mul_of_nonneg_left hL2 (abs_nonneg C')]

open Complex in
/-- **An explicit safe height for `ζ′/ζ`**, adapted from Tau Ceti Window.lean
(`riemannZeta_safe_height`, Apache 2.0, The Tau Ceti contributors). -/
theorem riemannZeta_safe_height_of {Cw Cc : ℝ}
    (hCw : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        Cw * Real.log (|s.im| + 2))
    (hCc : ∀ t : ℝ, ∑ z ∈ TauCeti.riemannZetaZerosClosedBall (2 + (t : ℂ) * I) (29 / 16),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ Cc * Real.log (|t| + 2)) :
    ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1), ∀ σ : ℝ, 1 / 4 ≤ σ → σ ≤ 2 →
      ∀ s ∈ ({(σ : ℂ) + (T' : ℂ) * I, (σ : ℂ) - (T' : ℂ) * I} : Set ℂ),
        riemannZeta s ≠ 0 ∧
          ‖deriv riemannZeta s / riemannZeta s‖ ≤
            (2 * |Cw| + 288 * Cc ^ 2 + 24 * |Cc| + 1) * Real.log (T + 2) ^ 2 := by
  classical
  intro T hT
  set Z := safe_Z T
  set K := ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hcard := safe_card_image_abs_im_le_sum (Z := Z) fun z hz ↦ by
    simp only [Z, safe_Z, Finset.mem_union] at hz
    rcases hz with ((((hz | hz) | hz) | hz) | hz) | hz <;>
      exact (TauCeti.mem_riemannZetaZerosClosedBall.1 hz).2
  obtain ⟨T', hT', hsepT'⟩ := TauCeti.exists_mem_Icc_forall_le_abs_sub
    (Z.image fun z ↦ |z.im|) (by linarith : T ≤ T + 1)
  have hδ : 1 / (2 * (K + 1)) ≤ (T + 1 - T) / (2 * ((Z.image fun z ↦ |z.im|).card + 1)) := by
    rw [add_sub_cancel_left]
    gcongr
  refine ⟨T', hT', fun σ hσ₁ hσ₂ s hs ↦ ?_⟩
  have hsre : s.re = σ := by rcases hs with rfl | rfl <;> simp
  have hsim : |s.im| = T' := by
    rcases hs with rfl | rfl <;> simp [abs_of_nonneg (by linarith [hT'.1] : (0 : ℝ) ≤ T')]
  have hsep (z : ℂ) (hz : z ∈ Z) : 1 / (2 * (K + 1)) ≤ ‖s - z‖ := by
    refine (hδ.trans (hsepT' _ (Finset.mem_image_of_mem _ hz))).trans ?_
    rw [← hsim]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by simpa using abs_im_le_norm (s - z))
  obtain ⟨hζ, hbound⟩ := safe_riemannZeta_ne_zero_and_norm_logDeriv_le hCw (Z := Z)
    (one_div_pos.2 (by linarith)) (hsre ▸ hσ₁) (hsre ▸ hσ₂) (by linarith [hT'.1])
    (fun z h1 h2 h3 h4 ↦ safe_mem_Z (hsim ▸ hT'.1) (hsim ▸ hT'.2) h1 h2 h3 h4) hsep
  refine ⟨hζ, hbound.trans ?_⟩
  have hlog : Real.log (|s.im| + 2) ≤ 2 * Real.log (T + 2) :=
    Real.log_add_two_le_two_mul_log_add_two (by linarith) (abs_nonneg _)
      (by linarith [hT'.2])
  have hKδ : K / (1 / (2 * (K + 1))) = 2 * K * (K + 1) := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [hKδ]
  exact safe_final_arith
    ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9]))
    (Real.log_nonneg (by linarith [abs_nonneg s.im])) hlog hK0 (safe_sum_Z_le hCc hT)

end WallsMeetRHExplicit

#print axioms WallsMeetRHExplicit.riemannZeta_safe_height_of

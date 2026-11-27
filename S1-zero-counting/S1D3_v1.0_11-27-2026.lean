/-
Schoenfeld S1, part D3: the argument bookkeeping for Backlund's bound on `S(T)`.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0; the
Tau Ceti modules used are Apache-2.0 (The Tau Ceti contributors).
-/
import SchoenfeldS1.D2
import TauCeti.NumberTheory.LFunctions.Zeros.RiemannVonMangoldt.Argument
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Target (D): `|S(T)| ≤ log((8T + 48)/(2 - π²/6))/log(5/4) + 3/2`, and `|S(T)| ≤ 4.5 log T + 17.08`

`S(T)` is Tau Ceti's `riemannZetaS T`, `π⁻¹` times the change of a continuous argument `θ` of `ζ`
along `2 → 2 + iT → 1/2 + iT` (`exists_riemannZetaS_eq_div_pi`, `θ 0 = 0`, `S(T) = θ 2/π`).

* Vertical segment (`t ∈ [0, 1]`): `Re ζ(2 + itT) ≥ 2 - π²/6 > 0` (`re_riemannZeta_two_add_ge`), so
  `cos (θ t) > 0`, and with `θ 0 = 0` the intermediate value theorem keeps `|θ t| < π/2`.
* Horizontal segment (`t ∈ [1, 2]`, `σ = 2 - 3(t - 1)/2`): `cos (θ t) = 0` exactly at the zeros of
  `Re ζ(σ + iT) = gB T σ` (`gB_eq_re_of_real`), which lie in the disc of radius `3/2` about `2`;
  Jensen (`card_zeros_gB_le`) bounds their number by `q := log((8T + 48)/(2 - π²/6))/log(5/4)`.
  Between consecutive zeros `cos (θ t) ≠ 0`, so `θ` moves by less than `π`
  (`abs_sub_le_pi_of_cos_ne_zero`), and by induction over the finite zero set
  `|θ 2 - θ 1| ≤ (q + 1) π`.
* Hence `|S(T)| = |θ 2|/π ≤ q + 3/2`. The numerical form uses `log(5/4) ≥ 0.22313`
  (`Real.abs_log_sub_add_sum_range_le`), `log(80/7) ≤ 2.44`, `log(2 - π²/6) ≥ -1.04`.
-/

namespace SchoenfeldS1

open Complex Real Metric Set
open TauCeti.LFunctions (riemannZetaS riemannZetaSPath riemannZetaSPath_of_le_one
  riemannZetaSPath_of_one_le exists_riemannZetaS_eq_div_pi riemannZeta_riemannZetaSPath_ne_zero)

local notation "ζ" => riemannZeta

/-- `T` is not an ordinate: `ζ` has no zero at height `T` with `1/2 ≤ Re s < 1` (Tau Ceti's
admissibility; by the functional equation this excludes every zero at height `T`). -/
def NotOrdinate (T : ℝ) : Prop := ∀ σ ∈ Ico (1 / 2 : ℝ) 1, ζ (σ + T * I) ≠ 0

/-! ### Real analysis: a continuous angle with controlled cosine -/

/-- A continuous `θ` on `[a, b]` with `θ a = 0` and `cos (θ t) > 0` throughout stays in
`(-π/2, π/2)`. -/
theorem abs_lt_pi_div_two_of_cos_pos {θ : ℝ → ℝ} {a b : ℝ} (hθ : ContinuousOn θ (Icc a b))
    (h0 : θ a = 0) (hcos : ∀ t ∈ Icc a b, 0 < Real.cos (θ t)) :
    ∀ t ∈ Icc a b, |θ t| < π / 2 := by
  intro t ht
  by_contra hcon
  rw [not_lt, le_abs] at hcon
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hθ' : ContinuousOn θ (Icc a t) := hθ.mono hsub
  rcases hcon with h | h
  · -- `θ t ≥ π/2`: `θ` takes the value `π/2` somewhere on `[a, t]`
    have hmem : π / 2 ∈ Icc (θ a) (θ t) := ⟨by rw [h0]; positivity, h⟩
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc ht.1 hθ' hmem
    have := hcos u (hsub hu)
    rw [hθu, Real.cos_pi_div_two] at this
    exact lt_irrefl _ this
  · -- `θ t ≤ -π/2`: `θ` takes the value `-π/2` somewhere on `[a, t]`
    have hmem : -(π / 2) ∈ Icc (θ t) (θ a) := ⟨by linarith, by rw [h0]; linarith [Real.pi_pos]⟩
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc' ht.1 hθ' hmem
    have := hcos u (hsub hu)
    rw [hθu, Real.cos_neg, Real.cos_pi_div_two] at this
    exact lt_irrefl _ this

/-- `cos` vanishes at `(k + 1/2) π`. -/
lemma cos_int_add_half_mul_pi (k : ℤ) : Real.cos ((2 * k + 1) * π / 2) = 0 :=
  Real.cos_eq_zero_iff.mpr ⟨k, rfl⟩

/-- If `x < y - π` then some `(k + 1/2) π` lies in `(x, y)`. -/
lemma exists_half_odd_mul_pi_mem_Ioo {x y : ℝ} (h : x + π < y) :
    ∃ k : ℤ, x < (2 * k + 1) * π / 2 ∧ (2 * k + 1) * π / 2 < y := by
  refine ⟨⌊x / π - 1 / 2⌋ + 1, ?_, ?_⟩
  · have h1 := Int.lt_floor_add_one (x / π - 1 / 2)
    have h2 : x / π * π = x := div_mul_cancel₀ x Real.pi_pos.ne'
    push_cast
    nlinarith [Real.pi_pos]
  · have h1 := Int.floor_le (x / π - 1 / 2)
    have h2 : x / π * π = x := div_mul_cancel₀ x Real.pi_pos.ne'
    push_cast
    nlinarith [Real.pi_pos]

/-- A continuous `θ` on `[a, b]` whose cosine does not vanish on `(a, b)` moves by at most `π`. -/
theorem abs_sub_le_pi_of_cos_ne_zero {θ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hθ : ContinuousOn θ (Icc a b)) (hcos : ∀ t ∈ Ioo a b, Real.cos (θ t) ≠ 0) :
    |θ b - θ a| ≤ π := by
  by_contra hcon
  rw [not_le, lt_abs] at hcon
  rcases hcon with h | h
  · obtain ⟨k, hk1, hk2⟩ := exists_half_odd_mul_pi_mem_Ioo (x := θ a) (y := θ b) (by linarith)
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc hab hθ ⟨hk1.le, hk2.le⟩
    have hua : u ≠ a := fun h => by rw [h] at hθu; linarith
    have hub : u ≠ b := fun h => by rw [h] at hθu; linarith
    exact hcos u ⟨lt_of_le_of_ne hu.1 (Ne.symm hua), lt_of_le_of_ne hu.2 hub⟩
      (by rw [hθu]; exact cos_int_add_half_mul_pi k)
  · obtain ⟨k, hk1, hk2⟩ := exists_half_odd_mul_pi_mem_Ioo (x := θ b) (y := θ a) (by linarith)
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc' hab hθ ⟨hk1.le, hk2.le⟩
    have hua : u ≠ a := fun h => by rw [h] at hθu; linarith
    have hub : u ≠ b := fun h => by rw [h] at hθu; linarith
    exact hcos u ⟨lt_of_le_of_ne hu.1 (Ne.symm hua), lt_of_le_of_ne hu.2 hub⟩
      (by rw [hθu]; exact cos_int_add_half_mul_pi k)

/-- A continuous `θ` on `[a, b]` whose cosine vanishes on `(a, b)` only at the points of a finite
set `Z` moves by at most `(|Z| + 1) π`. -/
theorem abs_sub_le_of_finite_cos_zero {θ : ℝ → ℝ} {a : ℝ} (Z : Finset ℝ) :
    ∀ {b : ℝ}, a ≤ b → ContinuousOn θ (Icc a b) → (∀ z ∈ Z, z ∈ Ioo a b) →
      (∀ t ∈ Ioo a b, t ∉ Z → Real.cos (θ t) ≠ 0) → |θ b - θ a| ≤ (Z.card + 1) * π := by
  induction Z using Finset.induction_on_max with
  | empty =>
    intro b hab hθ _ hcos
    simpa using abs_sub_le_pi_of_cos_ne_zero hab hθ (fun t ht => hcos t ht (by simp))
  | insert m Z hlt ih =>
    intro b hab hθ hZ hcos
    have hm : m ∈ Ioo a b := hZ m (Finset.mem_insert_self m Z)
    have hmZ : m ∉ Z := fun h => lt_irrefl m (hlt m h)
    -- on `[a, m]`
    have h1 := ih hm.1.le (hθ.mono (Icc_subset_Icc_right hm.2.le))
      (fun z hz => ⟨(hZ z (Finset.mem_insert_of_mem hz)).1, hlt z hz⟩)
      (fun t ht htZ => hcos t ⟨ht.1, ht.2.trans hm.2⟩ (by
        rw [Finset.mem_insert, not_or]; exact ⟨ht.2.ne, htZ⟩))
    -- on `[m, b]`
    have h2 := abs_sub_le_pi_of_cos_ne_zero hm.2.le (hθ.mono (Icc_subset_Icc_left hm.1.le))
      (fun t ht => hcos t ⟨hm.1.trans ht.1, ht.2⟩ (by
        rw [Finset.mem_insert, not_or]
        exact ⟨ht.1.ne', fun h => lt_asymm ht.1 (hlt t h)⟩))
    rw [Finset.card_insert_of_notMem hmZ]
    push_cast
    calc |θ b - θ a| = |(θ b - θ m) + (θ m - θ a)| := by ring_nf
      _ ≤ |θ b - θ m| + |θ m - θ a| := abs_add_le _ _
      _ ≤ π + (Z.card + 1) * π := add_le_add h2 h1
      _ = (Z.card + 1 + 1) * π := by ring

/-! ### The argument of `ζ` along `2 → 2 + iT → 1/2 + iT` -/

/-- The real part of a polar form is the norm times the cosine of the argument. -/
lemma re_eq_norm_mul_cos {z : ℂ} {x : ℝ} (h : z = ‖z‖ * exp (I * x)) :
    z.re = ‖z‖ * Real.cos x := by
  conv_lhs => rw [h]
  rw [mul_comm I, re_ofReal_mul, exp_ofReal_mul_I_re]

/-- **(D), Backlund's bound.** For `T ≥ 14` not an ordinate,
`|S(T)| ≤ log((8T + 48)/(2 - π²/6))/log(5/4) + 3/2`. -/
theorem abs_riemannZetaS_le_backlund {T : ℝ} (hT : 14 ≤ T) (hord : NotOrdinate T) :
    |riemannZetaS T| ≤ Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4) + 3 / 2 := by
  set q := Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4) with hq
  have hT0 : T ≠ 0 := by positivity
  have hT3 : 3 ≤ T := by linarith
  obtain ⟨θ, hθ, hlift, hθ0, hS⟩ := exists_riemannZetaS_eq_div_pi hT0 hord
  have hne : ∀ t ∈ Icc (0 : ℝ) 2, ζ (riemannZetaSPath T t) ≠ 0 := fun t ht =>
    riemannZeta_riemannZetaSPath_ne_zero hord ht.2
  have hre : ∀ t ∈ Icc (0 : ℝ) 2,
      (ζ (riemannZetaSPath T t)).re = ‖ζ (riemannZetaSPath T t)‖ * Real.cos (θ t) :=
    fun t ht => re_eq_norm_mul_cos (hlift t ht)
  -- vertical segment: `|θ 1| < π/2`
  have hvert : |θ 1| < π / 2 := by
    refine abs_lt_pi_div_two_of_cos_pos (a := 0) (b := 1)
      (hθ.mono (Icc_subset_Icc_right one_le_two)) hθ0 (fun t ht => ?_) 1 (right_mem_Icc.mpr zero_le_one)
    have ht2 : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1, ht.2.trans one_le_two⟩
    have hpos : 0 < (ζ (riemannZetaSPath T t)).re := by
      rw [riemannZetaSPath_of_le_one ht.2]
      have h := re_riemannZeta_two_add_ge (t * T)
      have h2 := two_sub_pi_sq_div_six_pos
      push_cast at h
      linarith
    rw [hre t ht2] at hpos
    exact pos_of_mul_pos_right hpos (norm_nonneg _)
  -- horizontal segment: the zeros of `cos θ` on `(1, 2)`
  let σ : ℝ → ℝ := fun t => 2 - 3 / 2 * (t - 1)
  have hpath : ∀ t, 1 ≤ t → riemannZetaSPath T t = (σ t : ℂ) + T * I := fun t ht => by
    rw [riemannZetaSPath_of_one_le ht]; simp only [σ]; push_cast; ring
  let Zt : Set ℝ := {t | t ∈ Ioo (1 : ℝ) 2 ∧ gB T (σ t) = 0}
  -- any finite subset of `Zt` has at most `q` elements
  have hcard : ∀ F : Finset ℝ, (↑F : Set ℝ) ⊆ Zt → (F.card : ℝ) ≤ q := by
    intro F hF
    have hinj : Function.Injective (fun t : ℝ => ((σ t : ℝ) : ℂ)) := by
      intro x y hxy
      have := ofReal_injective hxy
      simp only [σ] at this
      linarith
    have h := card_zeros_gB_le hT3 (F.image (fun t : ℝ => ((σ t : ℝ) : ℂ))) (by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨t, htF, rfl⟩ := hz
      have htZ : t ∈ Zt := hF htF
      refine ⟨?_, htZ.2⟩
      rw [mem_closedBall, dist_eq_norm, show ((σ t : ℝ) : ℂ) - 2 = ((σ t - 2 : ℝ) : ℂ) by push_cast; ring,
        norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> simp only [σ] <;> linarith [htZ.1.1, htZ.1.2])
    rwa [Finset.card_image_of_injective _ hinj] at h
  have hfin : Zt.Finite := by
    by_contra hinf
    obtain ⟨F, hFZ, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊q⌋₊ + 1)
    have h1 := hcard F hFZ
    rw [hFc] at h1
    push_cast at h1
    linarith [Nat.lt_floor_add_one q]
  have hZq : (hfin.toFinset.card : ℝ) ≤ q := hcard _ (by simp)
  have hhor : |θ 2 - θ 1| ≤ (hfin.toFinset.card + 1) * π := by
    refine abs_sub_le_of_finite_cos_zero (θ := θ) (a := 1) hfin.toFinset one_le_two
      (hθ.mono (Icc_subset_Icc_left zero_le_one)) (fun z hz => (hfin.mem_toFinset.mp hz).1)
      (fun t ht htZ hc => htZ ?_)
    rw [hfin.mem_toFinset]
    refine ⟨ht, ?_⟩
    have ht2 : t ∈ Icc (0 : ℝ) 2 := ⟨by linarith [ht.1], ht.2.le⟩
    have h := hre t ht2
    rw [hc, mul_zero, hpath t ht.1.le] at h
    rw [gB_eq_re_of_real, h, ofReal_zero]
  -- assemble
  have hq1 : (hfin.toFinset.card + 1) * π ≤ (q + 1) * π :=
    mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
  have hθ2 : |θ 2| ≤ (q + 3 / 2) * π := by
    calc |θ 2| = |(θ 2 - θ 1) + θ 1| := by ring_nf
      _ ≤ |θ 2 - θ 1| + |θ 1| := abs_add_le _ _
      _ ≤ (q + 1) * π + π / 2 := add_le_add (hhor.trans hq1) hvert.le
      _ = (q + 3 / 2) * π := by ring
  rw [hS, abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  exact hθ2

/-! ### Numerics -/

/-- `log(5/4) ≥ 0.22313`, from the alternating series with eight terms. -/
lemma log_five_div_four_ge : (0.22313 : ℝ) ≤ Real.log (5 / 4) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1 / 4) (by rw [abs_lt]; constructor <;> norm_num) 8
  have hs : ∑ i ∈ Finset.range 8, (-1 / 4 : ℝ) ^ (i + 1) / (i + 1) =
      -1 / 4 + 1 / 32 - 1 / 192 + 1 / 1024 - 1 / 5120 + 1 / 24576 - 1 / 114688 + 1 / 524288 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hs, show (1 : ℝ) - -1 / 4 = 5 / 4 by norm_num] at h
  have h2 : |(-1 / 4 : ℝ)| ^ (8 + 1) / (1 - |(-1 / 4 : ℝ)|) = 1 / 196608 := by norm_num
  rw [h2, abs_le] at h
  linarith [h.1]

/-- `log(80/7) ≤ 2.44`: `80/7 ≤ e² · e^{0.44}`. -/
lemma log_eighty_div_seven_le : Real.log (80 / 7) ≤ 2.44 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.sum_le_exp_of_nonneg (x := 0.44) (by norm_num) 5
  have hs : ∑ i ∈ Finset.range 5, (0.44 : ℝ) ^ i / (i.factorial : ℝ) =
      1 + 0.44 + 0.44 ^ 2 / 2 + 0.44 ^ 3 / 6 + 0.44 ^ 4 / 24 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hs] at h2
  have h3 : Real.exp 2.44 = Real.exp 1 * Real.exp 1 * Real.exp 0.44 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [h3]
  have h4 : (2.7182818283 : ℝ) * 2.7182818283 * (1 + 0.44 + 0.44 ^ 2 / 2 + 0.44 ^ 3 / 6 + 0.44 ^ 4 / 24)
      ≤ Real.exp 1 * Real.exp 1 * Real.exp 0.44 := by
    apply mul_le_mul (mul_le_mul h1.le h1.le (by norm_num) (Real.exp_pos _).le) h2 (by norm_num)
      (by positivity)
  linarith [h4]

/-- `log(2 - π²/6) ≥ -1.04`: `2 - π²/6 ≥ 0.355 ≥ e^{-1.04}`. -/
lemma log_two_sub_pi_sq_div_six_ge : (-1.04 : ℝ) ≤ Real.log (2 - π ^ 2 / 6) := by
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hm : (0.355 : ℝ) ≤ 2 - π ^ 2 / 6 := by nlinarith
  have h0 : (0 : ℝ) < 0.355 := by norm_num
  calc (-1.04 : ℝ) ≤ Real.log 0.355 := by
        rw [Real.le_log_iff_exp_le h0]
        have h1 := Real.exp_one_gt_d9
        have h2 := Real.add_one_le_exp (0.04 : ℝ)
        have h3 : Real.exp (-1.04) = 1 / (Real.exp 1 * Real.exp 0.04) := by
          rw [← Real.exp_add, Real.exp_neg, one_div]; norm_num
        rw [h3, div_le_iff₀ (by positivity)]
        nlinarith [Real.exp_pos 0.04]
    _ ≤ Real.log (2 - π ^ 2 / 6) := Real.log_le_log h0 hm

/-- `log T ≥ 2` for `T ≥ 14`. -/
lemma two_le_log_of_fourteen_le {T : ℝ} (hT : 14 ≤ T) : (2 : ℝ) ≤ Real.log T := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

/-- The numerical form of (D): `|S(T)| ≤ 4.5 log T + 17.08` for `T ≥ 14` not an ordinate. -/
theorem abs_riemannZetaS_le {T : ℝ} (hT : 14 ≤ T) (hord : NotOrdinate T) :
    |riemannZetaS T| ≤ 4.5 * Real.log T + 17.08 := by
  refine (abs_riemannZetaS_le_backlund hT hord).trans ?_
  have hm := two_sub_pi_sq_div_six_pos
  have hT0 : (0 : ℝ) < T := by linarith
  set l := Real.log T with hl
  have hl2 : 2 ≤ l := two_le_log_of_fourteen_le hT
  -- the numerator
  have hnum : Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) ≤ l + 3.48 := by
    rw [Real.log_div (by positivity) hm.ne']
    have h1 : Real.log (8 * T + 48) ≤ l + 2.44 := by
      calc Real.log (8 * T + 48) ≤ Real.log (T * (80 / 7)) :=
            Real.log_le_log (by positivity) (by nlinarith)
        _ = l + Real.log (80 / 7) := Real.log_mul hT0.ne' (by norm_num)
        _ ≤ l + 2.44 := by linarith [log_eighty_div_seven_le]
    linarith [log_two_sub_pi_sq_div_six_ge]
  have hnum0 : 0 ≤ Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hm]
    nlinarith [Real.pi_pos]
  have hden := log_five_div_four_ge
  have hB : Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4) ≤ (l + 3.48) / 0.22313 := by
    calc Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / Real.log (5 / 4)
        ≤ Real.log ((8 * T + 48) / (2 - π ^ 2 / 6)) / 0.22313 :=
          div_le_div_of_nonneg_left hnum0 (by norm_num) hden
      _ ≤ (l + 3.48) / 0.22313 := div_le_div_of_nonneg_right hnum (by norm_num)
  have hfin : (l + 3.48) / 0.22313 + 3 / 2 ≤ 4.5 * l + 17.08 := by
    rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

end SchoenfeldS1

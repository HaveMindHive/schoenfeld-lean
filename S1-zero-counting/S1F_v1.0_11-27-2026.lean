/-
Schoenfeld S1, part F: the zero-count lemmas of the ported S2 proof re-proved for the Backlund-type
error term `RtB T = 4.5 log T + 17.1` (in place of Hasanalizade-Shen-Wong's `Rt`), with the tail
threshold raised from `70` to `1000`.
Adapted from goldbach-lean (Steve Hubbard, Apache-2.0): `SchoenfeldPort/Dudek2014/SigmaHSW.lean`
and `SchoenfeldPort/PNTPort/ExplicitPsi1/FirstDiffHSW.lean` of the port
`~/HaveMindHive/schoenfeld-port_v1.0_11-27-2026/` (not modified there).
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the port,
Mathlib 31ce06ea and Tau Ceti, in the environment of the riemann-hypothesis-community repository
(Lean v4.37.0-rc1; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldPort.Final

/-!
# Zero-count lemmas with the Backlund-type error `RtB`

The port's `SigmaHSW.lean` and `FirstDiffHSW.lean` consume the zero count only through
`Mt T ± Rt T`, with `Rt T = 0.1038 log T + 0.2573 log log T + 10.2425`. This file redoes them with

`RtB T = 4.5 log T + 17.1`,

which is what a Backlund disc argument with the crude bound `‖ζ s‖ ≤ 8T + 48` on the disc of
radius `15/8` about `2 + iT` gives (S1D2), and raises the tail threshold `70` to `1000`
(`T = 2π√x/log x` is above `10^6` at `x ≥ 10^15`, so this costs nothing in S2).

Numerals (`A0 = 2 · 4.5 = 9`, `B0 = 2 · 17.1 + 7/4 ≤ 36`):
* `head_countB`: `#{|γ| ≤ T} ≤ T log T/π - (0.89 T - 36 - 9 log T)` for `T ≥ 1000`;
* `ATB T = 34.2 + 2 RtB T ≤ 9 log T + 68.4`; `H2B T T ≤ log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²`;
* `slackB`: `1.1 (18 log T + 72.9 - 0.25 T) ≤ 0.89 T - 36 - 9 log T` for `T ≥ 1000`;
* `count_majorB`: `2 (Mt t + RtB t) ≤ mFB t = t (log t - log 2π - 1)/π + 36 + 9 log t` for `t ≥ 14`;
* `head_invB`: `Σ_{14 ≤ |γ| ≤ T} 1/|γ| ≤ (log T - log 2π)²/(2π) + 4.8` for `T ≥ 14`;
* `zdiff_leB`: the first difference of the zero sum with `SB1 T = (log T - log 2π)²/(2π) + 4.8`
  and `SB2 T = log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²`, for `T ≥ 1000`.
-/

namespace SchoenfeldS1

open MeasureTheory Set Filter Topology Real
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt c_lower c_upper)
open SchoenfeldPort.Dudek2014.SigmaT (log_le_half integral_two_div_cube
  integrableOn_two_div_cube rhoF fz Zr wgt wgt_le wgt_le_inv_sq wgt_nonneg norm_fz_le'
  f1 rhoF_re rhoF_ne hasDerivAt_fz norm_cpow_rhoF norm_rho_mul_ge' norm_fz_le)
open SchoenfeldPort.Dudek2014.SigmaH (Mt_eq)
open SchoenfeldPort.PNTPort.ExplicitPsi1.FirstDiff (norm_rhoF_ge norm_rhoF_pos first_diff_small
  first_diff_large log_ge_14 one_div_sq_int)

variable {ι : Type*}

/-- The Backlund-type error term, `RtB T = 4.5 log T + 17.1`. -/
noncomputable def RtB (T : ℝ) : ℝ := 4.5 * log T + 17.1

/-- The two-sided count hypothesis for `T ≥ 1000`, both signs, finite sets (shape of the port's
`HSWN70` with `RtB`). -/
def NB1000 (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 1000 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + RtB T)) ∧
  (∀ T t : ℝ, 1000 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + RtB t) - (Mt T - RtB T)))

/-- The head clause for `T ≥ 14` (shape of the port's `HSWHead14` with `RtB`). -/
def NBHead14 (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, 14 ≤ T → ∀ s : Finset ι, ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + RtB T)

/-! ### Elementary log bounds -/

lemma log_ge_six {T : ℝ} (hT : 1000 ≤ T) : 6 ≤ log T := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  have e : exp 6 = exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 := by gcongr
  nlinarith

lemma log_1000_le : log (1000 : ℝ) ≤ 6.92 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have e : exp 6.92 = exp 1 ^ 7 * exp (-0.08) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 : (0.92 : ℝ) ≤ exp (-0.08) := by linarith [Real.add_one_le_exp (-0.08 : ℝ)]
  rw [e]
  have : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 := by gcongr
  nlinarith [Real.exp_pos (-0.08 : ℝ), pow_pos (Real.exp_pos 1) 7]

/-- `log T ≤ T/100` for `T ≥ 1000`. -/
lemma log_le_hundredth {T : ℝ} (hT : 1000 ≤ T) : log T ≤ T / 100 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / 1000)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  linarith [log_1000_le]

lemma RtB_nonneg {t : ℝ} (ht : 14 ≤ t) : 0 ≤ RtB t := by
  have := log_ge_14 ht
  unfold RtB; linarith

/-! ### The zero counts (SigmaHSW with `RtB`) -/

/-- The head count `#{|γ| ≤ T} ≤ T log T/π - (0.89 T - 36 - 9 log T)` for `T ≥ 1000`. -/
lemma head_countB {γ : ι → ℝ} (hN : NB1000 γ) {T : ℝ} (hT : 1000 ≤ T) (s : Finset ι) :
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤
      T * log T / π - (0.89 * T - 36 - 9 * log T) := by
  have hT0 : 0 < T := by linarith
  have h := hN.1 T hT s
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  rw [Mt_eq hT0] at h
  have e : 2 * (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 + RtB T) =
      T * log T / π - T * (log (2 * π) + 1) / π + (7 / 4 + 2 * RtB T) := by field_simp; ring
  rw [e] at h
  have h1 : 0.89 * T ≤ T * (log (2 * π) + 1) / π := by
    have hπ4 := Real.pi_lt_d4
    rw [le_div_iff₀ Real.pi_pos]
    have : 0 ≤ T * (log (2 * π) + 1 - 0.89 * π) := mul_nonneg hT0.le (by linarith)
    nlinarith
  unfold RtB at h
  linarith

/-- The constant part of the tail error, `A_T = 34.2 + 2 RtB(T)`. -/
noncomputable def ATB (T : ℝ) : ℝ := 34.2 + 2 * RtB T

/-- The majorant of the count times `2/t³`. -/
noncomputable def h2B (T t : ℝ) : ℝ :=
  ((t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π + 9 * log t + ATB T)
    * (2 / t ^ 3)

/-- Its tail integral. -/
noncomputable def H2B (T x : ℝ) : ℝ :=
  2 * (log x - log (2 * π)) / (π * x) - T * (log T - log (2 * π) - 1) / (π * x ^ 2)
    + 18 * (2 * log x + 1) / (4 * x ^ 2) + ATB T / x ^ 2

lemma hasDerivAt_negH2B (T : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => -H2B T y) (h2B T x) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have h1 := ((hl.sub_const (log (2 * π))).const_mul 2).div ((hasDerivAt_id x).const_mul π)
    (by rw [id]; positivity)
  have h2' := (hasDerivAt_const x (T * (log T - log (2 * π) - 1))).div
    ((hasDerivAt_pow 2 x).const_mul π) (by positivity)
  have h3 := ((hl.const_mul 2).add_const 1).const_mul 18 |>.div
    ((hasDerivAt_pow 2 x).const_mul 4) (by positivity)
  have h4 := (hasDerivAt_const x (ATB T)).div (hasDerivAt_pow 2 x) (by positivity)
  have h := (((h1.sub h2').add h3).add h4).neg
  convert h using 1
  · funext y
    simp only [H2B, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, id]
  · unfold h2B
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring

lemma tendsto_H2B (T : ℝ) : Tendsto (H2B T) atTop (𝓝 0) := by
  have a1 := SchoenfeldPort.ChirreHagen2025.Lemma26P.tendsto_log_pow_div 1
  have a0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have b1 := SchoenfeldPort.ChirreHagen2025.Lemma26P.tendsto_log_pow_div_sq 1
  have b0 := SchoenfeldPort.ChirreHagen2025.Lemma26P.tendsto_log_pow_div_sq 0
  have h := ((((a1.const_mul (2 / π)).sub (a0.const_mul (2 * log (2 * π) / π))).sub
    (b0.const_mul (T * (log T - log (2 * π) - 1) / π))).add
    ((b1.const_mul (18 * 2 / 4)).add (b0.const_mul (18 / 4)))).add (b0.const_mul (ATB T))
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [H2B, pow_one, pow_zero]
  field_simp

lemma ATB_le (T : ℝ) : ATB T ≤ 9 * log T + 68.4 := by
  unfold ATB RtB; linarith

lemma h2B_nonneg {T t : ℝ} (hT : 1000 ≤ T) (ht : T ≤ t) : 0 ≤ h2B T t := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hlT := log_ge_six hT
  have hlt := Real.log_le_log hT0 ht
  have hc := c_upper
  have hR := RtB_nonneg (by linarith : (14 : ℝ) ≤ T)
  unfold h2B ATB
  apply mul_nonneg _ (by positivity)
  have : 0 ≤ (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π := by
    apply div_nonneg _ Real.pi_pos.le
    nlinarith
  nlinarith

lemma integral_h2B {T : ℝ} (hT : 1000 ≤ T) :
    IntegrableOn (h2B T) (Ioi T) ∧ ∫ t in Ioi T, h2B T t = H2B T T := by
  have hT0 : 0 < T := by linarith
  have hc : ContinuousWithinAt (fun y => -H2B T y) (Ici T) T :=
    (hasDerivAt_negH2B T hT0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioi T, HasDerivAt (fun y => -H2B T y) (h2B T x) x :=
    fun x hx => hasDerivAt_negH2B T (by simp at hx; linarith)
  have hp : ∀ x ∈ Ioi T, 0 ≤ h2B T x := fun x hx => h2B_nonneg hT (le_of_lt hx)
  have hl : Tendsto (fun y => -H2B T y) atTop (𝓝 0) := by simpa using (tendsto_H2B T).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp hl]; ring

/-- `H2B(T, T) ≤ log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²`. -/
lemma H2B_bound {T : ℝ} (hT : 1000 ≤ T) :
    H2B T T ≤ log T / (π * T) + (18 * log T + 72.9 - 0.25 * T) / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hA := ATB_le T
  have hc := c_lower
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have e : H2B T T = log T / (π * T) - (log (2 * π) - 1) / (π * T)
      + (9 * log T + 4.5 + ATB T) / T ^ 2 := by
    unfold H2B; field_simp; ring
  rw [e]
  have h1 : 0.25 * T / T ^ 2 ≤ (log (2 * π) - 1) / (π * T) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0.25 * π ≤ log (2 * π) - 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ T ^ 2)
    nlinarith
  have h2' : (9 * log T + 4.5 + ATB T) / T ^ 2 ≤ (18 * log T + 72.9) / T ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have e2 : (18 * log T + 72.9 - 0.25 * T) / T ^ 2 =
      (18 * log T + 72.9) / T ^ 2 - 0.25 * T / T ^ 2 := by ring
  rw [e2]; linarith

/-- `Σ_{|γ| > T} 1/γ² ≤ log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²`, over any finite set. -/
lemma tail_inv_sqB {γ : ι → ℝ} (hN : NB1000 γ) {T : ℝ} (hT : 1000 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2) ≤
      log T / (π * T) + (18 * log T + 72.9 - 0.25 * T) / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => ¬ |γ i| ≤ T)
  obtain ⟨hhi, hhint⟩ := integral_h2B hT
  have hterm : ∀ i ∈ S, 1 / γ i ^ 2 =
      ∫ t in Ioi T, (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hg : T < |γ i| := lt_of_not_ge hi.2
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hg.le,
      integral_two_div_cube (by linarith), sq_abs]
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t)
      (volume.restrict (Ioi T)) :=
    fun i _ => (integrableOn_two_div_cube hT0).indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum S hint]
  refine (setIntegral_mono_on (integrable_finsetSum S hint) hhi measurableSet_Ioi
    fun t ht => ?_).trans (hhint.trans_le (H2B_bound hT))
  have ht' : T < t := ht
  have ht0 : 0 < t := by linarith
  have hφ : 0 ≤ 2 / t ^ 3 := by positivity
  have e : ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 2 / t ^ 3) t =
      ((S.filter (fun i => |γ i| < t)).card : ℝ) * (2 / t ^ 3) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : |γ i| < t
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [e]
  have hsub : S.filter (fun i => |γ i| < t) ⊆ s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t) := by
    intro i hi
    simp only [S, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1.1, lt_of_not_ge hi.1.2, hi.2.le⟩
  have hc1 : ((S.filter (fun i => |γ i| < t)).card : ℝ) ≤
      ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hc2 := hN.2 T t hT ht'.le s
  have hcount : ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤
      (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π + 9 * log t + ATB T := by
    rw [Mt_eq ht0, Mt_eq hT0] at hc2
    have e2 : 2 * ((t * (log t - log (2 * π) - 1) / (2 * π) + 7 / 8 + RtB t) -
        (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 - RtB T)) =
        (t * (log t - log (2 * π) - 1) - T * (log T - log (2 * π) - 1)) / π
          + 2 * RtB t + 2 * RtB T := by field_simp; ring
    rw [e2] at hc2
    have : 2 * RtB t = 9 * log t + 34.2 := by unfold RtB; ring
    unfold ATB; linarith
  unfold h2B
  exact mul_le_mul_of_nonneg_right (hc1.trans hcount) hφ

/-! ### The split, with the head slack paying for the tail -/

/-- The two error terms balance for `T ≥ 1000`: `0.89 T - 36 - 9 log T ≥ 0` and
`≥ 1.1 (18 log T + 72.9 - 0.25 T)`. -/
lemma slackB {T : ℝ} (hT : 1000 ≤ T) :
    0 ≤ 0.89 * T - 36 - 9 * log T ∧
      1.1 * (18 * log T + 72.9 - 0.25 * T) ≤ 0.89 * T - 36 - 9 * log T := by
  have hl := log_le_hundredth hT
  constructor <;> nlinarith

lemma split_boundB {γ : ι → ℝ} (hN : NB1000 γ) {T a b : ℝ} (hT : 1000 ≤ T) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : b ≤ 1.1 * a * T ^ 2) (F : ι → ℝ) (hFs : ∀ i, |γ i| ≤ T → F i ≤ a)
    (hFl : ∀ i, ¬ |γ i| ≤ T → F i ≤ b / γ i ^ 2) (s : Finset ι) :
    ∑ i ∈ s, F i ≤ T * log T / π * a + b * (log T / (π * T)) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hD0, hDE⟩ := slackB hT
  set D := 0.89 * T - 36 - 9 * log T
  set E := 18 * log T + 72.9 - 0.25 * T
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
  have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), F i ≤ (T * log T / π - D) * a := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), a :=
          Finset.sum_le_sum fun i hi => hFs i (Finset.mem_filter.mp hi).2
      _ = ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) * a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T * log T / π - D) * a := by gcongr; exact head_countB hN hT s
  have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), F i ≤ b * (log T / (π * T) + E / T ^ 2) := by
    calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), b * (1 / γ i ^ 2) :=
          Finset.sum_le_sum fun i hi => by
            have := hFl i (Finset.mem_filter.mp hi).2; rw [mul_one_div]; exact this
      _ = b * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ b * (log T / (π * T) + E / T ^ 2) := by gcongr; exact tail_inv_sqB hN hT s
  have h3 : b * (E / T ^ 2) ≤ D * a := by
    rcases le_or_gt E 0 with hE | hE
    · have : b * (E / T ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb (div_nonpos_of_nonpos_of_nonneg hE (by positivity))
      have := mul_nonneg hD0 ha
      linarith
    · have hT2 : 0 < T ^ 2 := by positivity
      have : b * (E / T ^ 2) ≤ 1.1 * a * E := by
        rw [mul_div_assoc', div_le_iff₀ hT2]
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left hDE ha
      have e4 : a * (1.1 * E) = 1.1 * a * E := by ring
      have e5 : a * D = D * a := by ring
      linarith
  have e6 : (T * log T / π - D) * a = T * log T / π * a - D * a := by ring
  have e7 : b * (log T / (π * T) + E / T ^ 2) = b * (log T / (π * T)) + b * (E / T ^ 2) := by ring
  linarith

lemma ne_of_largeB {γ : ι → ℝ} {T : ℝ} (hT : 1000 ≤ T) {i : ι} (hi : ¬ |γ i| ≤ T) : γ i ≠ 0 := by
  intro h; apply hi; rw [h, abs_zero]; linarith

lemma summable_wgtB {γ : ι → ℝ} (hN : NB1000 γ) : Summable (wgt γ) :=
  summable_of_sum_le (fun i => wgt_nonneg γ i) fun s =>
    split_boundB hN (a := 4 / 3) (b := 1) (le_refl 1000) (by norm_num) (by norm_num) (by norm_num)
      (wgt γ) (fun i _ => wgt_le γ i) (fun i hi => by
        exact wgt_le_inv_sq γ (ne_of_largeB (le_refl 1000) hi)) s

lemma summable_fzB {γ : ι → ℝ} (hN : NB1000 γ) {y : ℝ} (hy : 0 < y) :
    Summable (fun i => fz (rhoF (γ i)) y) :=
  Summable.of_norm_bounded ((summable_wgtB hN).mul_left (y ^ (3 / 2 : ℝ)))
    (fun i => norm_fz_le' (γ i) hy)

/-! ### The head sum `Σ 1/|γ|` (FirstDiffHSW with `RtB`) -/

/-- The count majorant `m(t) = t (log t - log 2π - 1)/π + 36 + 9 log t`. -/
noncomputable def mFB (t : ℝ) : ℝ := t * (log t - log (2 * π) - 1) / π + 36 + 9 * log t

/-- Its antiderivative against `1/t²`. -/
noncomputable def FFB (t : ℝ) : ℝ :=
  (log t - log (2 * π) - 1) ^ 2 / (2 * π) - 36 / t - 9 * (log t + 1) / t

/-- `2(M(t) + RtB(t)) ≤ m(t)` for `t ≥ 14`. -/
lemma count_majorB {t : ℝ} (ht : 14 ≤ t) : 2 * (Mt t + RtB t) ≤ mFB t := by
  have ht0 : 0 < t := by linarith
  rw [Mt_eq ht0]
  unfold mFB RtB
  have e : 2 * (t * (log t - log (2 * π) - 1) / (2 * π) + 7 / 8) =
      t * (log t - log (2 * π) - 1) / π + 7 / 4 := by field_simp; ring
  linarith

lemma hasDerivAt_FFB {t : ℝ} (ht : 0 < t) : HasDerivAt FFB (mFB t / t ^ 2) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have h1 := (((hl.sub_const (log (2 * π))).sub_const 1).pow 2).div_const (2 * π)
  have h2 := (hasDerivAt_id t).inv ht.ne' |>.const_mul 36
  have h3 := ((hl.add_const 1).const_mul 9).div (hasDerivAt_id t) ht.ne'
  have h := (h1.sub h2).sub h3
  convert h using 1
  · funext y; simp [FFB, div_eq_mul_inv]
  · unfold mFB; simp only [id, Nat.cast_ofNat]; field_simp; ring

lemma continuousOn_mFB_div : ContinuousOn (fun t => mFB t / t ^ 2) (Ici 1) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  apply ContinuousAt.continuousWithinAt
  unfold mFB
  have hlog : ContinuousAt log t := Real.continuousAt_log ht0.ne'
  apply ContinuousAt.div₀ _ (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')
  fun_prop (disch := exact ht0.ne')

/-- **`Σ_{14 ≤ |γ| ≤ T} 1/|γ| ≤ log²(T/2π)/(2π) + 4.8`** for `T ≥ 14`, from `NBHead14`. -/
lemma head_invB {γ : ι → ℝ} (hN : NBHead14 γ) (h14 : ∀ i, 14 ≤ |γ i|) {T : ℝ} (hT : 14 ≤ T)
    (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => |γ i| ≤ T), 1 / |γ i| ≤ (log T - log (2 * π)) ^ 2 / (2 * π) + 4.8 := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => |γ i| ≤ T)
  have hterm : ∀ i ∈ S, 1 / |γ i| =
      1 / T + ∫ t in Ioc 14 T, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, max_eq_right (h14 i),
      one_div_sq_int (by linarith [h14 i]) hi.2]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Icc 14 T) := fun t ht =>
    (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (by linarith [ht.1] : (0 : ℝ) < t).ne')).continuousWithinAt
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t)
      (volume.restrict (Ioc 14 T)) :=
    fun i _ => ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← integral_finsetSum S hint,
    Finset.sum_const, nsmul_eq_mul]
  have hmaj : IntegrableOn (fun t => mFB t / t ^ 2) (Ioc 14 T) :=
    ((continuousOn_mFB_div.mono (fun t ht => by simp only [mem_Ici]; linarith [ht.1])).integrableOn_Icc
      ).mono_set Ioc_subset_Icc_self
  have hI : ∫ t in Ioc 14 T, mFB t / t ^ 2 = FFB T - FFB 14 := by
    rw [← intervalIntegral.integral_of_le hT]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht; rw [uIcc_of_le hT] at ht; exact hasDerivAt_FFB (by linarith [ht.1])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact continuousOn_mFB_div.mono (fun t ht => by simp only [mem_Ici]; linarith [ht.1])
  have hle : ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t ≤
      ∫ t in Ioc 14 T, mFB t / t ^ 2 := by
    refine setIntegral_mono_on (integrable_finsetSum S hint) hmaj measurableSet_Ioc
      fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have e : ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t =
        ((S.filter (fun i => |γ i| < t)).card : ℝ) * (1 / t ^ 2) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : |γ i| < t
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [e, ← mul_one_div (mFB t)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hsub : S.filter (fun i => |γ i| < t) ⊆ s.filter (fun i => |γ i| ≤ t) := by
      intro i hi
      simp only [S, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2.le⟩
    have hc1 : ((S.filter (fun i => |γ i| < t)).card : ℝ) ≤ ((s.filter (fun i => |γ i| ≤ t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc1.trans ((hN t ht.1.le s).trans (count_majorB ht.1.le))
  have hcard : (S.card : ℝ) * (1 / T) ≤ mFB T * (1 / T) :=
    mul_le_mul_of_nonneg_right ((hN T hT s).trans (count_majorB hT)) (by positivity)
  have hfin : mFB T * (1 / T) + (FFB T - FFB 14) ≤ (log T - log (2 * π)) ^ 2 / (2 * π) + 4.8 := by
    have hl := log_ge_14 hT
    have hc := c_lower
    have hc' := c_upper
    have hπ := Real.pi_gt_three
    have hπ' := Real.pi_lt_d2
    have h14l : log 14 ≤ 2.7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.7)
      have e : exp 2.7 = exp 1 ^ 2 * exp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h1 := Real.exp_one_gt_d9
      have : (2.7182818283 : ℝ) ^ 2 ≤ exp 1 ^ 2 := by gcongr
      nlinarith
    have h14g := log_ge_14 (le_refl 14)
    have e1 : mFB T * (1 / T) = (log T - log (2 * π) - 1) / π + (36 + 9 * log T) / T := by
      unfold mFB; field_simp; ring
    have e2 : FFB T = (log T - log (2 * π) - 1) ^ 2 / (2 * π) - (36 + 9 * log T + 9) / T := by
      unfold FFB; field_simp; ring
    have e3 : FFB 14 ≥ -(36 + 9 * log 14 + 9) / 14 := by
      unfold FFB
      have : 0 ≤ (log 14 - log (2 * π) - 1) ^ 2 / (2 * π) := by positivity
      have e4 : -(36 + 9 * log 14 + 9) / 14 = -(36 / 14) - 9 * (log 14 + 1) / 14 := by
        ring
      linarith
    have e5 : (log T - log (2 * π) - 1) ^ 2 / (2 * π) + (log T - log (2 * π) - 1) / π =
        (log T - log (2 * π)) ^ 2 / (2 * π) - 1 / (2 * π) := by field_simp; ring
    have e6 : 9 / T ≥ 0 := by positivity
    have e7 : 1 / (2 * π) ≥ 0.158 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith
    have e8 : (36 + 9 * log 14 + 9) / 14 ≤ 4.95 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [e1, e2]
    have e9 : (36 + 9 * log T) / T - (36 + 9 * log T + 9) / T = -(9 / T) := by
      field_simp; ring
    linarith
  have hsum : (S.card : ℝ) * (1 / T) +
      ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t ≤
      mFB T * (1 / T) + (FFB T - FFB 14) := by rw [← hI]; linarith
  calc _ = (S.card : ℝ) * (1 / T) +
        ∫ t in Ioc 14 T, ∑ i ∈ S, (Ioi |γ i|).indicator (fun t => 1 / t ^ 2) t := by ring
    _ ≤ _ := hsum.trans hfin

/-! ### The first difference of the zero sum -/

/-- The head factor `S₁(T) = log²(T/2π)/(2π) + 4.8`. -/
noncomputable def SB1 (T : ℝ) : ℝ := (log T - log (2 * π)) ^ 2 / (2 * π) + 4.8

/-- The tail factor `S₂(T) = log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²`. -/
noncomputable def SB2 (T : ℝ) : ℝ := log T / (π * T) + (18 * log T + 72.9 - 0.25 * T) / T ^ 2

/-- **`|Σ_ρ (f(x + h) - f(x))| ≤ h (x + h)^{1/2} S₁(T) + 2 (x + h)^{3/2} S₂(T)`** for `T ≥ 1000`,
for any ordinate family with the `RtB` counts and every `|γ| ≥ 14`. -/
theorem zdiff_leB {γ : ι → ℝ} (hN : NB1000 γ) (hH : NBHead14 γ)
    (h14 : ∀ i, 14 ≤ |γ i|) {x h T : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hT : 1000 ≤ T) :
    ‖(∑' i, fz (rhoF (γ i)) (x + h)) - ∑' i, fz (rhoF (γ i)) x‖ ≤
      h * (x + h) ^ (1 / 2 : ℝ) * SB1 T + 2 * (x + h) ^ (3 / 2 : ℝ) * SB2 T := by
  have hxh : 0 < x + h := by linarith
  set D : ι → ℂ := fun i => fz (rhoF (γ i)) (x + h) - fz (rhoF (γ i)) x
  have sa := summable_fzB hN hxh
  have sb := summable_fzB hN hx
  have eD : (∑' i, fz (rhoF (γ i)) (x + h)) - ∑' i, fz (rhoF (γ i)) x = ∑' i, D i :=
    (sa.tsum_sub sb).symm
  rw [eD]
  set B := 2 * (x + h) ^ (3 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  set a := h * (x + h) ^ (1 / 2 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hne : ∀ i, γ i ≠ 0 := fun i h0 => by have := h14 i; rw [h0, abs_zero] at this; linarith
  have hDn : ∀ i, ‖D i‖ ≤ B * wgt γ i := fun i => by
    have := first_diff_large (γ i) hx hh
    unfold wgt; rw [mul_one_div]; exact this
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn ((summable_wgtB hN).mul_left B)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤ a * SB1 T + B * SB2 T := by
    intro s
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
    have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), ‖D i‖ ≤ a * SB1 T := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T), a * (1 / |γ i|) := by
            apply Finset.sum_le_sum; intro i _
            have h0 : 0 < |γ i| := abs_pos.mpr (hne i)
            have := first_diff_small (γ i) hx hh
            refine this.trans ?_
            rw [← mul_div_assoc, mul_one_div]
            exact div_le_div_of_nonneg_left ha h0 (norm_rhoF_ge _)
        _ = a * ∑ i ∈ s.filter (fun i => |γ i| ≤ T), 1 / |γ i| := by rw [Finset.mul_sum]
        _ ≤ a * SB1 T := by gcongr; exact head_invB hH h14 (by linarith) s
    have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), ‖D i‖ ≤ B * SB2 T := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), B * (1 / γ i ^ 2) := by
            apply Finset.sum_le_sum; intro i _
            exact (hDn i).trans (mul_le_mul_of_nonneg_left (wgt_le_inv_sq γ (hne i)) hB)
        _ = B * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
        _ ≤ B * SB2 T := by gcongr; exact tail_inv_sqB hN hT s
    linarith
  calc ‖∑' i, D i‖ ≤ ∑' i, ‖D i‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ a * SB1 T + B * SB2 T := hsumN.tsum_le_of_sum_le hfin

end SchoenfeldS1

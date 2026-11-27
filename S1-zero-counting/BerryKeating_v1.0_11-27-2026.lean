/-
Schoenfeld S1, Berry-Keating smooth counting law: for every `T ≥ 14`,
`|N(T) - ((T/2π) log(T/2π) - T/2π + 7/8)| ≤ 4.5 log T + 17.1`, at every `T` (ordinates included),
and the mean level density corollary for `N(T+1) - N(T)`.
AI-written Lean code (Claude), 11-27-2026. Environment: the riemann-hypothesis-community repository
(Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti; RH: Alpöge with Claude). Apache-2.0.
-/
import SchoenfeldS1.C

namespace SchoenfeldS1

open Complex Real Set Filter Topology
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt)

local notation "ζ" => riemannZeta

/-- The Berry-Keating smooth count `(T/2π) log(T/2π) - T/2π + 7/8`. -/
noncomputable def bkMain (T : ℝ) : ℝ := T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8

lemma Mt_eq_bkMain {T : ℝ} (hT : 0 < T) : Mt T = bkMain T := by
  unfold Mt bkMain
  rw [show T / (2 * π * Real.exp 1) = T / (2 * π) / Real.exp 1 by ring,
    Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-- Lower bound (L') for every `T > 14`: left limits through non-ordinates, `NT` monotone. -/
theorem Mt_sub_RtB_le_NT_of_lt {T : ℝ} (hT : 14 < T) : Mt T - RtB T ≤ NT T := by
  set a := max (T - 1) 14 with ha
  have haT : a < T := max_lt (by linarith) hT
  have ha14 : 14 ≤ a := le_max_right _ _
  have hcont : Tendsto (fun T' => Mt T' - RtB T') (𝓝[<] T) (𝓝 (Mt T - RtB T)) :=
    (((continuousAt_Mt (by linarith)).sub (continuousAt_RtB (by linarith))).tendsto).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  have h1 : ∀ᶠ T' in 𝓝[<] T, T' ∈ Ioo a T := Ioo_mem_nhdsLT haT
  have h2 : ∀ᶠ T' in 𝓝[<] T, ∀ ρ ∈ zerosBandF a T, ρ.im < T' ∨ ρ.im = T := by
    rw [Filter.eventually_all_finset]
    intro ρ hρ
    rcases (mem_zerosBandF.mp hρ).2.2.2.2.lt_or_eq with hlt | heq
    · exact ((eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => Or.inl h
    · exact Filter.Eventually.of_forall fun _ => Or.inr heq
  filter_upwards [h1, h2] with T' hT' hρ
  have hord : NotOrdinate T' := notOrdinate_of_no_zero fun σ h0 h1 hz => by
    have := hρ _ (mem_zerosBandF_of_zero hz h0 h1 hT'.1 hT'.2.le)
    simp only [ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
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

/-- Lower bound (L') at `T = 14`: `Mt 14 ≤ 7/8` since `14 < 2πe`. -/
lemma Mt_sub_RtB_le_NT_fourteen : Mt 14 - RtB 14 ≤ NT 14 := by
  have hpi := Real.pi_gt_three
  have he := Real.exp_one_gt_d9
  have hlog : Real.log (14 / (2 * π * Real.exp 1)) < 0 := by
    apply Real.log_neg (by positivity)
    rw [div_lt_one (by positivity)]
    nlinarith
  have hl14 : 0 ≤ Real.log 14 := Real.log_nonneg (by norm_num)
  have hM : Mt 14 ≤ 7 / 8 := by
    unfold Mt
    have : 0 ≤ (14 : ℝ) / (2 * π) := by positivity
    nlinarith
  unfold RtB
  have : (0 : ℝ) ≤ NT 14 := Nat.cast_nonneg _
  linarith

/-- **Berry-Keating smooth counting law.** For every `T ≥ 14` (ordinates included),
`|N(T) - ((T/2π) log(T/2π) - T/2π + 7/8)| ≤ 4.5 log T + 17.1`. -/
theorem berry_keating_count {T : ℝ} (hT : 14 ≤ T) :
    |(NT T : ℝ) - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)|
      ≤ 4.5 * Real.log T + 17.1 := by
  have e := Mt_eq_bkMain (T := T) (by linarith)
  unfold bkMain at e
  rw [← e, abs_le]
  have hU := NT_le_Mt_add_RtB hT
  have hL : Mt T - RtB T ≤ NT T := by
    rcases hT.lt_or_eq with h | h
    · exact Mt_sub_RtB_le_NT_of_lt h
    · subst h; exact Mt_sub_RtB_le_NT_fourteen
  unfold RtB at hU hL
  constructor <;> linarith

/-- The increment of the smooth count over `[T, T+1]` lies between `log(T/2π)/2π` and
`log((T+1)/2π)/2π`. -/
lemma bkMain_succ_sub {T : ℝ} (hT : 0 < T) :
    Real.log (T / (2 * π)) / (2 * π) ≤ bkMain (T + 1) - bkMain T ∧
      bkMain (T + 1) - bkMain T ≤ Real.log ((T + 1) / (2 * π)) / (2 * π) := by
  have hpi := Real.pi_pos
  have h2pi : 0 < 2 * π := by positivity
  have hT1 : 0 < T + 1 := by linarith
  set L0 := Real.log (T / (2 * π))
  set L1 := Real.log ((T + 1) / (2 * π))
  have hd : L1 - L0 = Real.log ((T + 1) / T) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have key : bkMain (T + 1) - bkMain T = (L1 + T * (L1 - L0) - 1) / (2 * π) := by
    unfold bkMain; field_simp; ring
  have up : T * (L1 - L0) ≤ 1 := by
    rw [hd]
    have := Real.log_le_sub_one_of_pos (x := (T + 1) / T) (by positivity)
    have e : (T + 1) / T - 1 = 1 / T := by field_simp; ring
    rw [e] at this
    calc T * Real.log ((T + 1) / T) ≤ T * (1 / T) := by gcongr
      _ = 1 := by field_simp
  have lo : 1 ≤ (T + 1) * (L1 - L0) := by
    have := Real.log_le_sub_one_of_pos (x := T / (T + 1)) (by positivity)
    have e1 : Real.log (T / (T + 1)) = -(L1 - L0) := by
      rw [hd, ← Real.log_inv, inv_div]
    have e2 : T / (T + 1) - 1 = -(1 / (T + 1)) := by field_simp; ring
    rw [e1, e2] at this
    have h3 : 1 / (T + 1) ≤ L1 - L0 := by linarith
    calc (1 : ℝ) = (T + 1) * (1 / (T + 1)) := by field_simp
      _ ≤ (T + 1) * (L1 - L0) := by gcongr
  rw [key]
  constructor
  · rw [div_le_div_iff_of_pos_right h2pi]; nlinarith
  · rw [div_le_div_iff_of_pos_right h2pi]; nlinarith

/-- **Mean level density.** For `T ≥ 14`,
`log(T/2π)/2π - (9 log(T+1) + 34.2) ≤ N(T+1) - N(T) ≤ log((T+1)/2π)/2π + 9 log(T+1) + 34.2`. -/
theorem berry_keating_density {T : ℝ} (hT : 14 ≤ T) :
    Real.log (T / (2 * π)) / (2 * π) - (9 * Real.log (T + 1) + 34.2)
        ≤ (NT (T + 1) : ℝ) - NT T ∧
      (NT (T + 1) : ℝ) - NT T
        ≤ Real.log ((T + 1) / (2 * π)) / (2 * π) + 9 * Real.log (T + 1) + 34.2 := by
  have h0 := berry_keating_count hT
  have h1 := berry_keating_count (T := T + 1) (by linarith)
  have hd := bkMain_succ_sub (T := T) (by linarith)
  have hlog : Real.log T ≤ Real.log (T + 1) := Real.log_le_log (by linarith) (by linarith)
  unfold bkMain at hd
  rw [abs_le] at h0 h1
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, hd.1, hd.2]

end SchoenfeldS1

#print axioms SchoenfeldS1.berry_keating_count
#print axioms SchoenfeldS1.berry_keating_density

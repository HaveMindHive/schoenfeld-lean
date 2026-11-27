/-
Schoenfeld S1, part A: the counting bridge.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against the ported
goldbach-lean modules (SchoenfeldPort, Steve Hubbard, Apache-2.0), Mathlib 31ce06ea and Tau Ceti,
in the environment of the riemann-hypothesis-community repository (Lean v4.37.0-rc1). Apache-2.0.
-/
import SchoenfeldPort.Final

/-!
# From the zero count `N(T)` to the three hypotheses of `schoenfeld_psi_large`

The ported theorem `SchoenfeldPort.schoenfeld_psi_large` needs `HSWN70 gZ`, `HSWHead14 gZ` and
`Ordinates14 gZ`, all statements about finite sets of the index type
`ZIdx = Σ ρ : Zall, Fin (analyticOrderNatAt ζ ρ)` with `gZ i = Im ρ`. This file reduces them to
statements about one real function, the classical zero count

`NT T = Σ_{ρ : ζ ρ = 0, 0 < Re ρ < 1, 0 < Im ρ ≤ T} analyticOrderNatAt ζ ρ`

(zeros in the open critical strip of height in `(0, T]`, with multiplicity):

* `card_filter_le_two_mul_Nband`: for every finite `s : Finset ZIdx` and `0 ≤ a`,
  `#{i ∈ s | a < |gZ i| ≤ b} ≤ 2 · Nband a b`, where `Nband a b` counts the zeros with
  `a < Im ρ ≤ b`. The factor `2` is the reflection `ρ ↦ 1 - ρ` (the functional equation,
  `SchoenfeldPort.PNTPort.ZetaZeros.ord_one_sub` for the multiplicity), which carries the zeros of
  negative height onto those of positive height. No Riemann hypothesis is used.
* `HSWHead14_of_NT`: `(∀ T ≥ 14, NT T ≤ Mt T + Rt T) → HSWHead14 gZ`.
* `HSWN70_of_NT`: `(∀ T ≥ 70, NT T ≤ Mt T + Rt T) → (∀ T ≥ 70, Mt T - Rt T ≤ NT T) → HSWN70 gZ`.
* `Ordinates14_of_zeroFree`: `(∀ ρ, ζ ρ = 0 → 0 < Re ρ → Re ρ < 1 → 14 ≤ |Im ρ|) → Ordinates14 gZ`.

That `ζ` has no real zero in `(0, 1)` is `TauCeti.riemannZeta_lt_zero`.
-/

namespace SchoenfeldS1

open Complex Finset
open scoped ComplexOrder
open SchoenfeldPort.PNTPort.ExplicitPsi1 (Zall Zall_eq Zall_re_lt zeros_rect_finite)
open SchoenfeldPort.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)
open SchoenfeldPort.ChirreHagen2025.Lemma26H (Mt Rt)

local notation "ζ" => riemannZeta

/-- The zeros of `ζ` in the open critical strip with `a < Im ρ ≤ b`. -/
def zerosBand (a b : ℝ) : Set ℂ :=
  {ρ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < ρ.im ∧ ρ.im ≤ b}

lemma zerosBand_finite (a b : ℝ) : (zerosBand a b).Finite := by
  apply (zeros_rect_finite 2 (|a| + |b|)).subset
  rintro ρ ⟨hz, h0, h1, ha, hb⟩
  refine ⟨?_, hz⟩
  rw [Complex.Rectangle, Complex.mem_reProdIm]
  constructor
  · simp only [Set.mem_uIcc]; left; constructor <;> linarith
  · simp only [Set.mem_uIcc]; left
    constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

/-- The finite set of zeros of `ζ` in the open critical strip with `a < Im ρ ≤ b`. -/
noncomputable def zerosBandF (a b : ℝ) : Finset ℂ := (zerosBand_finite a b).toFinset

lemma mem_zerosBandF {a b : ℝ} {ρ : ℂ} :
    ρ ∈ zerosBandF a b ↔ ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < ρ.im ∧ ρ.im ≤ b := by
  simp [zerosBandF, zerosBand]

/-- `N(a, b)`: the zeros of `ζ` in the open critical strip with `a < Im ρ ≤ b`, with
multiplicity. -/
noncomputable def Nband (a b : ℝ) : ℕ := ∑ ρ ∈ zerosBandF a b, analyticOrderNatAt ζ ρ

/-- The classical zero count `N(T)`: zeros in the open critical strip with `0 < Im ρ ≤ T`, with
multiplicity. -/
noncomputable def NT (T : ℝ) : ℕ := Nband 0 T

/-- `N(0, t) = N(0, T) + N(T, t)` for `0 ≤ T ≤ t`. -/
lemma Nband_add {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) : Nband 0 t = Nband 0 T + Nband T t := by
  unfold Nband
  rw [← Finset.sum_union]
  · congr 1; ext ρ
    simp only [Finset.mem_union, mem_zerosBandF]
    constructor
    · rintro ⟨hz, h0, h1, hp, hb⟩
      by_cases h : ρ.im ≤ T
      · exact Or.inl ⟨hz, h0, h1, hp, h⟩
      · exact Or.inr ⟨hz, h0, h1, not_le.mp h, hb⟩
    · rintro (⟨hz, h0, h1, hp, hb⟩ | ⟨hz, h0, h1, hp, hb⟩)
      · exact ⟨hz, h0, h1, hp, hb.trans hTt⟩
      · exact ⟨hz, h0, h1, by linarith [hp], hb⟩
  · rw [Finset.disjoint_left]
    intro ρ h1 h2
    rw [mem_zerosBandF] at h1 h2
    linarith [h1.2.2.2.2, h2.2.2.2.1]

lemma NT_sub {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) : (NT t : ℝ) - NT T = Nband T t := by
  unfold NT; rw [Nband_add hT hTt]; push_cast; ring

/-- The defining properties of a point of `Zall`, through `Zall_eq`. -/
lemma zall_prop (ρ : Zall) : ζ (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
  (Set.ext_iff.mp Zall_eq (ρ : ℂ)).mp ρ.2

/-- No zero of `ζ` in the open critical strip is real (`TauCeti.riemannZeta_lt_zero`). -/
lemma im_ne_zero_of_zero {ρ : ℂ} (hz : ζ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.im ≠ 0 := by
  intro him
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have := TauCeti.riemannZeta_lt_zero h0 h1
  rw [← hρ, hz] at this
  exact lt_irrefl _ this

/-- The reflection `ρ ↦ 1 - ρ` is a bijection from the zeros of height in `[-b, -a)` onto the
zeros of height in `(a, b]`, preserving the multiplicity. -/
lemma sum_image_one_sub (a b : ℝ) :
    ∑ ρ ∈ (zerosBandF a b).image (fun ρ => 1 - ρ), analyticOrderNatAt ζ ρ
      = ∑ ρ ∈ zerosBandF a b, analyticOrderNatAt ζ ρ := by
  rw [Finset.sum_image (fun x _ y _ h => by linear_combination -h)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_zerosBandF] at hρ
  exact SchoenfeldPort.PNTPort.ZetaZeros.ord_one_sub hρ.2.1 hρ.2.2.1

/-- The two-sided zero set of heights `a < |Im ρ| ≤ b` with `0 ≤ a`, as the positive band and
its reflection; the two parts are disjoint. -/
lemma disjoint_zerosBandF_image {a b : ℝ} (ha : 0 ≤ a) :
    Disjoint (zerosBandF a b) ((zerosBandF a b).image (fun ρ => 1 - ρ)) := by
  rw [Finset.disjoint_left]
  intro ρ h1 h2
  rw [Finset.mem_image] at h2
  obtain ⟨σ, hσ, rfl⟩ := h2
  rw [mem_zerosBandF] at h1 hσ
  have : (1 - σ).im = -σ.im := by simp
  linarith [h1.2.2.2.1, hσ.2.2.2.1]

/-- **The counting bridge.** For every finite set `s` of indexed zeros and `0 ≤ a`,
`#{i ∈ s | a < |gZ i| ≤ b} ≤ 2 · N(a, b)`. -/
theorem card_filter_le_two_mul_Nband (s : Finset ZIdx) {a b : ℝ} (ha : 0 ≤ a) :
    (s.filter (fun i => a < |gZ i| ∧ |gZ i| ≤ b)).card ≤ 2 * Nband a b := by
  classical
  set P := zerosBandF a b with hP
  set t : Finset ℂ := P ∪ P.image (fun ρ => 1 - ρ) with ht
  -- the index `i` lies over a zero of the two-sided set `t`, with its multiplicity index
  let f : ZIdx → Σ _ : ℂ, ℕ := fun i => ⟨(i.1 : ℂ), i.2.val⟩
  have hmaps : Set.MapsTo f (s.filter (fun i => a < |gZ i| ∧ |gZ i| ≤ b))
      (t.sigma (fun ρ => Finset.range (analyticOrderNatAt ζ ρ))) := by
    intro i hi
    rw [Finset.coe_filter] at hi
    obtain ⟨-, hai, hib⟩ := hi
    obtain ⟨hz, h0, h1⟩ := zall_prop i.1
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range, f]
    refine ⟨?_, i.2.2⟩
    rw [ht, Finset.mem_union]
    have hg : gZ i = (i.1 : ℂ).im := rfl
    rw [hg] at hai hib
    rcases lt_or_gt_of_ne (im_ne_zero_of_zero hz h0 h1) with hneg | hpos
    · right
      rw [Finset.mem_image]
      refine ⟨1 - (i.1 : ℂ), ?_, by ring⟩
      rw [hP, mem_zerosBandF]
      refine ⟨SchoenfeldPort.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hz, ?_, ?_, ?_, ?_⟩
      · simp; linarith
      · simp; linarith
      · simp; rw [abs_of_neg hneg] at hai; linarith
      · simp; rw [abs_of_neg hneg] at hib; linarith
    · left
      rw [hP, mem_zerosBandF]
      rw [abs_of_pos hpos] at hai hib
      exact ⟨hz, h0, h1, hai, hib⟩
  have hinj : Set.InjOn f (s.filter (fun i => a < |gZ i| ∧ |gZ i| ≤ b)) := by
    rintro ⟨ρ₁, k₁⟩ - ⟨ρ₂, k₂⟩ - h
    simp only [f, Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have : ρ₁ = ρ₂ := Subtype.ext h1
    subst this
    rw [Fin.ext h2]
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_sigma] at hcard
  simp only [Finset.card_range] at hcard
  rw [ht, Finset.sum_union (disjoint_zerosBandF_image ha), sum_image_one_sub] at hcard
  unfold Nband
  omega

/-- The filter `|gZ i| ≤ T` equals the filter `0 < |gZ i| ≤ T`: no indexed zero has `Im ρ = 0`. -/
lemma filter_abs_le_eq (s : Finset ZIdx) (T : ℝ) :
    s.filter (fun i => |gZ i| ≤ T) = s.filter (fun i => 0 < |gZ i| ∧ |gZ i| ≤ T) := by
  apply Finset.filter_congr
  intro i _
  obtain ⟨hz, h0, h1⟩ := zall_prop i.1
  have hne : gZ i ≠ 0 := im_ne_zero_of_zero hz h0 h1
  exact ⟨fun h => ⟨abs_pos.mpr hne, h⟩, fun h => h.2⟩

/-- `#{i ∈ s | |gZ i| ≤ T} ≤ 2 N(T)`. -/
theorem card_filter_abs_le_le (s : Finset ZIdx) (T : ℝ) :
    ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T := by
  rw [filter_abs_le_eq]
  have := card_filter_le_two_mul_Nband s (a := 0) (b := T) le_rfl
  unfold NT
  exact_mod_cast this

/-- **`HSWHead14` from the upper bound on `N(T)`.** -/
theorem HSWHead14_of_NT (h : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T) :
    SchoenfeldPort.PNTPort.ExplicitPsi1.FirstDiff.HSWHead14 gZ := by
  intro T hT s
  calc ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T := card_filter_abs_le_le s T
    _ ≤ 2 * (Mt T + Rt T) := by linarith [h T hT]

/-- **`HSWN70` from the two-sided bound on `N(T)`.** -/
theorem HSWN70_of_NT (hU : ∀ T : ℝ, 70 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T)
    (hL : ∀ T : ℝ, 70 ≤ T → Mt T - Rt T ≤ NT T) :
    SchoenfeldPort.Dudek2014.SigmaH.HSWN70 gZ := by
  constructor
  · intro T hT s
    calc ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T := card_filter_abs_le_le s T
      _ ≤ 2 * (Mt T + Rt T) := by linarith [hU T hT]
  · intro T t hT hTt s
    have h1 := card_filter_le_two_mul_Nband s (a := T) (b := t) (by linarith)
    have h2 : ((s.filter (fun i => T < |gZ i| ∧ |gZ i| ≤ t)).card : ℝ) ≤ 2 * Nband T t := by
      exact_mod_cast h1
    rw [← NT_sub (by linarith) hTt] at h2
    linarith [hU t (by linarith), hL T hT]

/-- **`Ordinates14` from the absence of zeros of height below `14`.** -/
theorem Ordinates14_of_zeroFree
    (h : ∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 14 ≤ |ρ.im|) :
    SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ := by
  intro i
  obtain ⟨hz, h0, h1⟩ := zall_prop i.1
  exact h _ hz h0 h1

/-- `Ordinates14` from `N(14) = 0`. -/
theorem Ordinates14_of_NT (h : NT 14 = 0) :
    SchoenfeldPort.ChirreHagen2025.SmoothT2.Ordinates14 gZ := by
  apply Ordinates14_of_zeroFree
  intro ρ hz h0 h1
  by_contra hlt
  rw [not_le] at hlt
  -- a zero of height `|Im ρ| < 14` gives a zero of height in `(0, 14)`, counted in `N(14)`
  have hne := im_ne_zero_of_zero hz h0 h1
  obtain ⟨σ, hσ⟩ : ∃ σ, σ ∈ zerosBandF 0 14 := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine ⟨1 - ρ, ?_⟩
      rw [mem_zerosBandF]
      refine ⟨SchoenfeldPort.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hz, ?_, ?_, ?_, ?_⟩
      · simp; linarith
      · simp; linarith
      · simp; linarith
      · simp; rw [abs_of_neg hneg] at hlt; linarith
    · refine ⟨ρ, ?_⟩
      rw [mem_zerosBandF]
      rw [abs_of_pos hpos] at hlt
      exact ⟨hz, h0, h1, hpos, hlt.le⟩
  have hord : 1 ≤ analyticOrderNatAt ζ σ := by
    rw [mem_zerosBandF] at hσ
    apply SchoenfeldPort.PNTPort.ZetaZeros.ord_pos hσ.1
    intro h1'
    have := congr_arg Complex.re h1'
    simp at this; linarith [hσ.2.2.1]
  unfold NT Nband at h
  have : analyticOrderNatAt ζ σ ≤ 0 := by
    rw [← h]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hσ
  omega

end SchoenfeldS1

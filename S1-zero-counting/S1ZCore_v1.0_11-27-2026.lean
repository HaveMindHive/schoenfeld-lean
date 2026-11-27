/-
Schoenfeld S1, part Z (core): certified evaluation of zeta on the critical line.
AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel against Mathlib 31ce06ea and
Tau Ceti (The Tau Ceti contributors, Apache-2.0; its first-order Euler-Maclaurin zeta formula
`TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le` and its general Euler-Maclaurin formula
`TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt` are used, not copied), in the environment of the
riemann-hypothesis-community repository (Lean v4.37.0-rc1). Apache-2.0.
-/
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import Mathlib
open Complex Finset

/-!
# Certified evaluation of `ζ(1/2 + it)`

* `norm_zeta_sub_AEM_le`: the Euler-Maclaurin formula of order 4 for `ζ(s)`, `0 < Re s`, `s ≠ 1`,
  cut at `N` with an explicit remainder (Bernoulli `B₂`, `B₄` terms; `|B₄({x})| ≤ 1/30`), obtained
  from Tau Ceti's first-order formula cut at a large `M` and the order-4 formula on `[N, M]`.
* `norm_zeta_sub_Az_le`: on `s = 1/2 + it`, `0 ≤ t ≤ b ≤ 14`, with `N = 6`, `M = 10^12`:
  `‖ζ(s) - Az t‖ ≤ C · 1000/1333039680 + 1/40000` whenever `C² ≥ ∏_{j<4} ((j+1/2)² + b²)`.
* `Az_lip`: `‖Az t - Az u‖ ≤ Lrat λ (1/2 + b) · |t - u|` on `[a, b]`, `λ² ≤ 1/4 + a²`.
* Ball arithmetic (`taylor_ball_r`, `ball_sqi`, `ex_ball`, `Az_ball`): a rational enclosure of
  `Az tk` from Taylor polynomials of `exp(iφ)` and repeated squaring.
* `pt_cert`: one interval `[a, b]` is zero-free once the rational inequalities hold.
-/

namespace SchoenfeldS1.Z

lemma bernoulliFun_four (x : ℝ) : bernoulliFun 4 x = x^4 - 2*x^3 + x^2 - 30⁻¹ := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, bernoulli_four,
    bernoulli_three, bernoulli_two, Nat.choose]
  ring

lemma abs_bernoulliFun_four_fract_le (x : ℝ) : |bernoulliFun 4 (Int.fract x)| ≤ 1 / 30 := by
  rw [bernoulliFun_four]
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  set y := Int.fract x
  have hu : 0 ≤ y * (1 - y) := mul_nonneg h0 (by linarith)
  have hu' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1/2)]
  have : y^4 - 2*y^3 + y^2 = (y * (1 - y))^2 := by ring
  rw [abs_le]; constructor <;> nlinarith

lemma sum_Icc_int (f : ℤ → ℂ) (N M : ℕ) :
    ∑ j ∈ Icc (N:ℤ) M, f j = ∑ n ∈ Icc N M, f n := by
  have : Icc (N:ℤ) M = (Icc N M).map Nat.castEmbedding := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_map, Nat.castEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨j.toNat, by omega, by omega⟩
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩; omega
  rw [this, Finset.sum_map]; rfl

/-- The coefficients `c_i = (-s)(-s-1)...(-s-i+1)` of the derivatives of `x^(-s)`. -/
def cc (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | i + 1 => cc s i * (-s - i)

/-- The derivative family `g_i(x) = c_i x^(-s-i)` of `x ↦ x^(-s)`. -/
noncomputable def gg (s : ℂ) (i : ℕ) (x : ℝ) : ℂ := cc s i * (x : ℂ) ^ (-s - i)

lemma hasDerivAt_gg {s : ℂ} (hs : 0 < s.re) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gg s i) (gg s (i + 1) x) x := by
  have hr : (-s - i : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have h := (hasDerivAt_ofReal_cpow_const hx.ne' hr).const_mul (cc s i)
  have e : gg s (i + 1) x = cc s i * ((-s - i) * (x : ℂ) ^ (-s - i - 1)) := by
    simp only [gg, cc]; push_cast; ring_nf
  rw [e]; exact h

lemma norm_gg {s : ℂ} (i : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖gg s i x‖ = ‖cc s i‖ * x ^ (-s.re - i) := by
  rw [gg, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  congr 2

/-- The Euler-Maclaurin approximant of order 4 cut at `N`. -/
noncomputable def AEM (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (-s) / 2 + (N : ℂ) ^ (1 - s) / (s - 1)
    + s * (N : ℂ) ^ (-s - 1) / 12 - s * (s + 1) * (s + 2) * (N : ℂ) ^ (-s - 3) / 720

theorem norm_zeta_sub_AEM_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖riemannZeta s - AEM N s‖ ≤ ‖s‖ * (M : ℝ) ^ (-s.re) / (2 * s.re)
      + ‖s‖ * (M : ℝ) ^ (-s.re - 1) / 12 + ‖s * (s + 1) * (s + 2)‖ * (M : ℝ) ^ (-s.re - 3) / 720
      + ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (N : ℝ) ^ (-s.re - 3) / (720 * (s.re + 3)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hMpos : (0 : ℝ) < M := hNpos.trans_le hNM'
  have hpos : ∀ x ∈ Set.Icc (N:ℝ) M, 0 < x := fun x hx => hNpos.trans_le hx.1
  -- Euler-Maclaurin of order 4 on [N, M]
  have hEM := TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := gg s) (a := (N:ℤ)) (n := (M:ℤ))
    (by exact_mod_cast hNM) (k := 4) (by norm_num)
    (fun i _ x hx => (hasDerivAt_gg hs i (hpos x (by simpa using hx))).continuousAt.continuousWithinAt)
    (fun i _ x hx => hasDerivAt_gg hs i (hpos x ⟨by simpa using hx.1.le, by simpa using hx.2.le⟩))
    (ContinuousOn.intervalIntegrable (fun x hx =>
      (hasDerivAt_gg hs 4 (hpos x (by
        rw [Set.uIcc_of_le (by simpa using hNM')] at hx; simpa using hx))).continuousAt.continuousWithinAt))
  simp only [Int.cast_natCast] at hEM
  rw [sum_Icc_int (fun j => gg s 0 j)] at hEM
  have hI : ∫ x in (N:ℝ)..M, gg s 0 x = (N : ℂ) ^ (1 - s) / (s - 1) - (M : ℂ) ^ (1 - s) / (s - 1) := by
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [gg, cc, Nat.cast_zero, sub_zero, one_mul]
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), by
      rw [Set.uIcc_of_le hNM']; exact fun h => (lt_irrefl _ (hNpos.trans_le h.1))⟩)]
    have h1s : (1 - s : ℂ) ≠ 0 := fun h => hs1' (by linear_combination -h)
    simp only [Complex.ofReal_natCast]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    field_simp
    ring
  rw [hI, show Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide] at hEM
  simp only [Finset.sum_insert (show (2:ℕ) ∉ ({3, 4} : Finset ℕ) by decide),
    Finset.sum_insert (show (3:ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.sum_singleton,
    bernoulli_two, bernoulli_three, bernoulli_four, Complex.real_smul] at hEM
  set Iint := ∫ x in (N:ℝ)..M, bernoulliFun 4 (Int.fract x) • gg s 4 x with hIint
  -- the zeta formula cut at M
  have hZ := TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le (N := M) (by omega) hs hs1
  set R1 := riemannZeta s - (∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) + (M : ℂ) ^ (1 - s) / (s - 1) -
      (M : ℂ) ^ (-s) / 2) with hR1
  have hsplit : ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (-s) + ∑ n ∈ Finset.Icc N M, (n : ℂ) ^ (-s) := by
    have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := Finset.Icc_succ_left_eq_Ioc _ _
    have e2 : Finset.Icc 1 N = Finset.Ioc 0 N := Finset.Icc_succ_left_eq_Ioc _ _
    rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNM, Finset.Icc_eq_cons_Ioc hNM,
      Finset.sum_cons]
    ring
  have hgg : ∀ n : ℕ, gg s 0 (n : ℝ) = (n : ℂ) ^ (-s) := fun n => by simp [gg, cc]
  simp only [Int.cast_natCast, hgg] at hEM
  have e1 : ∀ x : ℝ, gg s 1 x = -s * (x : ℂ) ^ (-s - 1) := fun x => by
    simp only [gg, cc]; push_cast; ring_nf
  have e3 : ∀ x : ℝ, gg s 3 x = -(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3) := fun x => by
    simp only [gg, cc]; push_cast; ring_nf
  have key : riemannZeta s - AEM N s = R1 + (1/12 : ℂ) * gg s 1 M - (1/720 : ℂ) * gg s 3 M
      - (1/24 : ℂ) * Iint := by
    simp only [Nat.add_one_sub_one] at hEM
    rw [hR1, AEM, hsplit, hIint]
    simp only [e1, e3] at hEM ⊢
    simp only [Complex.ofReal_natCast, Complex.real_smul] at hEM ⊢
    norm_num [Nat.factorial] at hEM
    linear_combination hEM
  have hc4 : cc s 4 = s * (s + 1) * (s + 2) * (s + 3) := by simp only [cc]; push_cast; ring
  have hInt : ‖Iint‖ ≤ 1 / 30 * ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (N : ℝ) ^ (-s.re - 3) / (s.re + 3) := by
    have hb : ‖Iint‖ ≤ ∫ x in (N:ℝ)..M, (1 / 30 * ‖cc s 4‖) * x ^ (-s.re - 4) := by
      rw [hIint]
      refine intervalIntegral.norm_integral_le_of_norm_le hNM' (Filter.Eventually.of_forall ?_) ?_
      · intro x hx
        have hx0 : 0 < x := hNpos.trans hx.1
        rw [norm_smul, Real.norm_eq_abs, norm_gg 4 hx0]
        have := abs_bernoulliFun_four_fract_le x
        have h2 : 0 ≤ ‖cc s 4‖ * x ^ (-s.re - (4:ℕ)) := by positivity
        push_cast at h2 ⊢
        nlinarith
      · refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
        rw [Set.uIcc_of_le hNM'] at hx
        have hx0 : 0 < x := hNpos.trans_le hx.1
        exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne'))).continuousWithinAt
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hNM']; exact fun h => (lt_irrefl _ (hNpos.trans_le h.1))⟩), hc4] at hb
    have hM0 : 0 ≤ (M : ℝ) ^ (-s.re - 4 + 1) := by positivity
    have hpos3 : 0 < s.re + 3 := by linarith
    have : ((M : ℝ) ^ (-s.re - 4 + 1) - (N : ℝ) ^ (-s.re - 4 + 1)) / (-s.re - 4 + 1)
        ≤ (N : ℝ) ^ (-s.re - 3) / (s.re + 3) := by
      rw [show -s.re - 4 + 1 = -(s.re + 3) by ring, div_neg, ← neg_div, neg_sub, show -(s.re + 3) = -s.re - 3 by ring]
      rw [show -s.re - 4 + 1 = -s.re - 3 by ring] at hM0
      exact div_le_div_of_nonneg_right (by linarith) hpos3.le
    calc ‖Iint‖ ≤ _ := hb
      _ ≤ 1 / 30 * ‖s * (s + 1) * (s + 2) * (s + 3)‖ * ((N : ℝ) ^ (-s.re - 3) / (s.re + 3)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hg1 : ‖gg s 1 M‖ = ‖s‖ * (M : ℝ) ^ (-s.re - 1) := by
    rw [norm_gg 1 hMpos]
    have : cc s 1 = -s := by simp [cc]
    rw [this, norm_neg]; push_cast; rfl
  have hg3 : ‖gg s 3 M‖ = ‖s * (s + 1) * (s + 2)‖ * (M : ℝ) ^ (-s.re - 3) := by
    rw [norm_gg 3 hMpos]
    have : cc s 3 = -(s * (s + 1) * (s + 2)) := by simp only [cc]; push_cast; ring
    rw [this, norm_neg]; push_cast; rfl
  rw [key]
  clear_value R1 Iint
  calc ‖R1 + (1/12 : ℂ) * gg s 1 M - (1/720 : ℂ) * gg s 3 M - (1/24 : ℂ) * Iint‖
      ≤ ‖R1‖ + ‖(1/12 : ℂ) * gg s 1 M‖ + ‖(1/720 : ℂ) * gg s 3 M‖ + ‖(1/24 : ℂ) * Iint‖ := by
        have t1 := norm_sub_le (R1 + (1/12 : ℂ) * gg s 1 M - (1/720 : ℂ) * gg s 3 M) ((1/24 : ℂ) * Iint)
        have t2 := norm_sub_le (R1 + (1/12 : ℂ) * gg s 1 M) ((1/720 : ℂ) * gg s 3 M)
        have t3 := norm_add_le R1 ((1/12 : ℂ) * gg s 1 M)
        linarith
    _ ≤ _ := by
        rw [norm_mul, norm_mul, norm_mul, hg1, hg3]
        have n12 : ‖(1/12 : ℂ)‖ = 1/12 := by norm_num
        have n720 : ‖(1/720 : ℂ)‖ = 1/720 := by norm_num
        have n24 : ‖(1/24 : ℂ)‖ = 1/24 := by norm_num
        rw [n12, n720, n24]
        have e : 1 / 24 * (1 / 30 * ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (N : ℝ) ^ (-s.re - 3) / (s.re + 3))
          = ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (N : ℝ) ^ (-s.re - 3) / (720 * (s.re + 3)) := by
          field_simp; ring
        have h24 := mul_le_mul_of_nonneg_left hInt (by norm_num : (0:ℝ) ≤ 1/24)
        rw [e] at h24
        have e2 : 1 / 12 * (‖s‖ * (M : ℝ) ^ (-s.re - 1)) = ‖s‖ * (M : ℝ) ^ (-s.re - 1) / 12 := by ring
        have e3 : 1 / 720 * (‖s * (s + 1) * (s + 2)‖ * (M : ℝ) ^ (-s.re - 3))
          = ‖s * (s + 1) * (s + 2)‖ * (M : ℝ) ^ (-s.re - 3) / 720 := by ring
        rw [e2, e3]
        linarith

lemma norm_mk_le (a b : ℝ) : ‖(⟨a, b⟩ : ℂ)‖ ≤ |a| + |b| := by
  simpa using Complex.norm_le_abs_re_add_abs_im (⟨a, b⟩ : ℂ)

lemma ball_round {z : ℂ} {a b r a' b' r' : ℝ} (h : ‖z - ⟨a, b⟩‖ ≤ r)
    (hc : |a - a'| + |b - b'| + r ≤ r') : ‖z - ⟨a', b'⟩‖ ≤ r' := by
  have : z - ⟨a', b'⟩ = (z - ⟨a, b⟩) + ⟨a - a', b - b'⟩ := by apply Complex.ext <;> simp
  rw [this]
  linarith [norm_add_le (z - ⟨a, b⟩) ⟨a - a', b - b'⟩, norm_mk_le (a - a') (b - b')]

lemma ball_sq {z : ℂ} {a b r a' b' r' : ℝ} (h : ‖z - ⟨a, b⟩‖ ≤ r)
    (hc : |a * a - b * b - a'| + |2 * a * b - b'| + r * (2 * (|a| + |b|) + r) ≤ r') :
    ‖z ^ 2 - ⟨a', b'⟩‖ ≤ r' := by
  have hr : 0 ≤ r := (norm_nonneg _).trans h
  have e : z ^ 2 - ⟨a', b'⟩ = (z - ⟨a, b⟩) * ((z - ⟨a, b⟩) + 2 * ⟨a, b⟩)
      + ⟨a * a - b * b - a', 2 * a * b - b'⟩ := by
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [e]
  have h1 : ‖(z - ⟨a, b⟩) * ((z - ⟨a, b⟩) + 2 * ⟨a, b⟩)‖ ≤ r * (r + 2 * (|a| + |b|)) := by
    rw [norm_mul]
    have : ‖(z - ⟨a, b⟩) + 2 * (⟨a, b⟩ : ℂ)‖ ≤ r + 2 * (|a| + |b|) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]; simp only [Complex.norm_ofNat]
      linarith [norm_mk_le a b]
    exact mul_le_mul h this (norm_nonneg _) hr
  linarith [norm_add_le ((z - ⟨a, b⟩) * ((z - ⟨a, b⟩) + 2 * ⟨a, b⟩))
    (⟨a * a - b * b - a', 2 * a * b - b'⟩ : ℂ), norm_mk_le (a * a - b * b - a') (2 * a * b - b')]

/-- Taylor polynomials of cos and sin of degree 11. -/
noncomputable def Pc (φ : ℝ) : ℝ := 1 - φ^2/2 + φ^4/24 - φ^6/720 + φ^8/40320 - φ^10/3628800
noncomputable def Ps (φ : ℝ) : ℝ := φ - φ^3/6 + φ^5/120 - φ^7/5040 + φ^9/362880 - φ^11/39916800

lemma sum_exp_I (φ : ℝ) :
    ∑ m ∈ Finset.range 12, (I * φ) ^ m / (m.factorial : ℂ) = ⟨Pc φ, Ps φ⟩ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow]
  have p : ∀ k : ℕ, I ^ (4 * k) = 1 := fun k => by rw [pow_mul]; simp
  have q : ∀ k r : ℕ, I ^ (4 * k + r) = I ^ r := fun k r => by rw [pow_add, p, one_mul]
  have i3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have i4 : I ^ 4 = 1 := by rw [show (4:ℕ) = 4 * 1 + 0 from rfl, q]; simp
  have i5 : I ^ 5 = I := by rw [show (5:ℕ) = 4 * 1 + 1 from rfl, q]; simp
  have i6 : I ^ 6 = -1 := by rw [show (6:ℕ) = 4 * 1 + 2 from rfl, q]; simp
  have i7 : I ^ 7 = -I := by rw [show (7:ℕ) = 4 * 1 + 3 from rfl, q]; simp
  have i8 : I ^ 8 = 1 := by rw [show (8:ℕ) = 4 * 2 + 0 from rfl, q]; simp
  have i9 : I ^ 9 = I := by rw [show (9:ℕ) = 4 * 2 + 1 from rfl, q]; simp
  have i10 : I ^ 10 = -1 := by rw [show (10:ℕ) = 4 * 2 + 2 from rfl, q]; simp
  have i11 : I ^ 11 = -I := by rw [show (11:ℕ) = 4 * 2 + 3 from rfl, q]; simp
  simp only [i3, i4, i5, i6, i7, i8, i9, i10, i11, I_sq]
  apply Complex.ext <;> simp [Pc, Ps, Nat.factorial, ← Complex.ofReal_pow] <;> ring

lemma taylor_ball {φ : ℝ} (hφ : |φ| ≤ 1) :
    ‖cexp (I * φ) - ⟨Pc φ, Ps φ⟩‖ ≤ |φ| ^ 12 * (13 / 5748019200) := by
  have hx : ‖I * (φ : ℂ)‖ = |φ| := by simp
  have := Complex.exp_bound (x := I * φ) (by rw [hx]; exact hφ) (n := 12) (by norm_num)
  rw [sum_exp_I, hx] at this
  convert this using 2
  norm_num [Nat.factorial]



/-! ## The approximant on the critical line -/

noncomputable def sl (t : ℝ) : ℂ := 1 / 2 + t * I

@[simp] lemma sl_re (t : ℝ) : (sl t).re = 1 / 2 := by simp [sl]
@[simp] lemma sl_im (t : ℝ) : (sl t).im = t := by simp [sl]

lemma sl_ne_one (t : ℝ) : sl t ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this

noncomputable def Qf (s : ℂ) : ℂ := 1 / 2 + 6 / (s - 1) + s / 72 - s * (s + 1) * (s + 2) / 155520
noncomputable def Qd (s : ℂ) : ℂ := -6 / (s - 1) ^ 2 + 1 / 72 - (3 * s ^ 2 + 6 * s + 2) / 155520

noncomputable def Qre (t : ℝ) : ℝ :=
  1 / 2 - 3 / (1 / 4 + t ^ 2) + 1 / 144 - (15 / 8 - 9 * t ^ 2 / 2) / 155520
noncomputable def Qim (t : ℝ) : ℝ :=
  -6 * t / (1 / 4 + t ^ 2) + t / 72 - (23 * t / 4 - t ^ 3) / 155520

lemma Qf_sl (t : ℝ) : Qf (sl t) = ⟨Qre t, Qim t⟩ := by
  have h : (1 / 4 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have h' : sl t - 1 ≠ 0 := sub_ne_zero.mpr (sl_ne_one t)
  have e : 6 / (sl t - 1) = ⟨-3 / (1 / 4 + t ^ 2), -6 * t / (1 / 4 + t ^ 2)⟩ := by
    rw [div_eq_iff h']
    apply Complex.ext <;> simp [sl] <;> field_simp <;> ring
  rw [Qf, e]
  apply Complex.ext <;> simp [Qre, Qim, sl, pow_succ] <;> ring

noncomputable def ex (n : ℕ) (t : ℝ) : ℂ := (n : ℂ) ^ (-sl t)

noncomputable def Az (t : ℝ) : ℂ := 1 + ex 2 t + ex 3 t + ex 4 t + ex 5 t + ex 6 t * Qf (sl t)

lemma AEM_six {s : ℂ} (hs1 : s ≠ 1) :
    AEM 6 s = 1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s) + (4 : ℂ) ^ (-s) + (5 : ℂ) ^ (-s)
      + (6 : ℂ) ^ (-s) * Qf s := by
  have h6 : (6 : ℂ) ≠ 0 := by norm_num
  have hs : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have e1 : (6 : ℂ) ^ (1 - s) = 6 * (6 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ h6, cpow_one]
  have e2 : (6 : ℂ) ^ (-s - 1) = (6 : ℂ) ^ (-s) / 6 := by
    rw [cpow_sub _ _ h6, cpow_one]
  have e3 : (6 : ℂ) ^ (-s - 3) = (6 : ℂ) ^ (-s) / 216 := by
    rw [cpow_sub _ _ h6, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]; norm_num
  rw [AEM, show Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [e1, e2, e3, Qf, one_cpow]
  field_simp
  ring

lemma ex_eq (n : ℕ) (hn : 0 < n) (t : ℝ) : ex n t = cexp (-(sl t) * (Real.log n : ℂ)) := by
  rw [ex, cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), mul_comm]
  congr 2
  rw [← ofReal_natCast, ofReal_log (Nat.cast_nonneg n)]

noncomputable def rho (n : ℕ) : ℝ := Real.exp (-(1 / 2) * Real.log n)

lemma ex_split (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ex n t = (rho n : ℂ) * cexp (I * ((-(t * Real.log n) : ℝ) : ℂ)) := by
  rw [ex_eq n hn, rho, ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [sl]; push_cast; ring

lemma norm_ex (n : ℕ) (hn : 0 < n) (t : ℝ) : ‖ex n t‖ = rho n := by
  rw [ex_split n hn, norm_mul, norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_of_pos (Real.exp_pos _)

lemma rho_sq (n : ℕ) (hn : 0 < n) : rho n ^ 2 = 1 / n := by
  rw [rho, sq, ← Real.exp_add, show -(1 / 2) * Real.log n + -(1 / 2) * Real.log n = -Real.log n by ring,
    Real.exp_neg, Real.exp_log (by exact_mod_cast hn), one_div]

lemma rho_bounds (n : ℕ) (hn : 0 < n) {p q : ℝ} (hp : 0 ≤ p) (hp2 : p ^ 2 ≤ 1 / n)
    (hq : 0 ≤ q) (hq2 : 1 / n ≤ q ^ 2) : p ≤ rho n ∧ rho n ≤ q := by
  have h := rho_sq n hn
  have h0 : 0 < rho n := Real.exp_pos _
  constructor <;> nlinarith


/-! ## The error of the approximant on the critical line -/

lemma Az_eq (t : ℝ) : Az t = 1 + (2 : ℂ) ^ (-sl t) + (3 : ℂ) ^ (-sl t) + (4 : ℂ) ^ (-sl t)
    + (5 : ℂ) ^ (-sl t) + (6 : ℂ) ^ (-sl t) * Qf (sl t) := by
  simp [Az, ex]

lemma norm_sl_add_le (t : ℝ) (j : ℝ) (hj : 0 ≤ j) : ‖sl t + j‖ ≤ j + 1 / 2 + |t| := by
  have : sl t + j = ((j + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by simp [sl]; ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma normSq_sl_add (t j : ℝ) : ‖sl t + j‖ ^ 2 = (j + 1 / 2) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [sl]; ring

lemma le_of_sq_le_sq' {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C ^ 2) : x ≤ C := by
  nlinarith

theorem norm_zeta_sub_Az_le {t b C : ℝ} (ht0 : 0 ≤ t) (htb : t ≤ b) (hb : b ≤ 14) (hC : 0 ≤ C)
    (hCb : (1 / 4 + b ^ 2) * (9 / 4 + b ^ 2) * (25 / 4 + b ^ 2) * (49 / 4 + b ^ 2) ≤ C ^ 2) :
    ‖riemannZeta (sl t) - Az t‖ ≤ C * (1000 / 1333039680) + 1 / 40000 := by
  have h := norm_zeta_sub_AEM_le (N := 6) (M := 10 ^ 12) (by norm_num) (by norm_num) (s := sl t)
    (by simp) (sl_ne_one t)
  rw [AEM_six (sl_ne_one t), ← Az_eq] at h
  simp only [sl_re] at h
  have hb0 : 0 ≤ b := ht0.trans htb
  have hM : (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) = 1 / 10 ^ 6 := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show (((10 ^ 12 : ℕ) : ℝ)) = ((10:ℝ) ^ 6) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
    norm_num
  have hM1 : (1:ℝ) ≤ ((10 ^ 12 : ℕ) : ℝ) := by norm_num
  have hMa : (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 1) ≤ 1 / 10 ^ 6 := by
    rw [← hM]; exact Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
  have hMb : (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 3) ≤ 1 / 10 ^ 6 := by
    rw [← hM]; exact Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
  have h6 : (((6 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 3) ≤ 1000 / (216 * 2449) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hs : (2449 / 1000 : ℝ) ≤ Real.sqrt 6 := Real.le_sqrt_of_sq_le (by norm_num)
    have : (((6 : ℕ) : ℝ)) ^ (3 : ℝ) = 216 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [this]; push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (Real.sqrt 6)⁻¹ := by positivity
    rw [inv_eq_one_div] at *
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have hs1 : ‖sl t‖ ≤ 1 / 2 + b := by
    have := norm_sl_add_le t 0 le_rfl; simp at this; rw [abs_of_nonneg ht0] at this; linarith
  have hsj : ∀ j : ℝ, 0 ≤ j → ‖sl t + j‖ ≤ j + 1 / 2 + b := fun j hj => by
    have := norm_sl_add_le t j hj; rw [abs_of_nonneg ht0] at this; linarith
  have hs3 : ‖sl t * (sl t + 1) * (sl t + 2)‖ ≤ (1 / 2 + b) * (3 / 2 + b) * (5 / 2 + b) := by
    rw [norm_mul, norm_mul]
    have e1 := hsj 1 (by norm_num); have e2 := hsj 2 (by norm_num)
    push_cast at e1 e2
    have := mul_le_mul hs1 e1 (norm_nonneg _) (by linarith)
    have := mul_le_mul this e2 (norm_nonneg _) (by positivity)
    linarith
  have hs4 : ‖sl t * (sl t + 1) * (sl t + 2) * (sl t + 3)‖ ≤ C := by
    apply le_of_sq_le_sq' (norm_nonneg _) hC
    rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
    have e0 := normSq_sl_add t 0; have e1 := normSq_sl_add t 1
    have e2 := normSq_sl_add t 2; have e3 := normSq_sl_add t 3
    push_cast at e0 e1 e2 e3; simp only [add_zero] at e0
    rw [e0, e1, e2, e3]
    have ht2 : t ^ 2 ≤ b ^ 2 := by nlinarith
    refine le_trans ?_ hCb
    gcongr <;> nlinarith
  have hsnn : 0 ≤ ‖sl t‖ := norm_nonneg _
  have k1 : ‖sl t‖ * (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 * (1 / 2)) ≤ (1 / 2 + b) / 10 ^ 6 := by
    rw [hM]; norm_num; linarith
  have k2 : ‖sl t‖ * (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 1) / 12 ≤ (1 / 2 + b) / 10 ^ 6 / 12 := by
    have := mul_le_mul hs1 hMa (by positivity) (by linarith)
    rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
  have k3 : ‖sl t * (sl t + 1) * (sl t + 2)‖ * (((10 ^ 12 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 3) / 720
      ≤ (1 / 2 + b) * (3 / 2 + b) * (5 / 2 + b) / 10 ^ 6 / 720 := by
    have := mul_le_mul hs3 hMb (by positivity) (by positivity)
    rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
  have k4 : ‖sl t * (sl t + 1) * (sl t + 2) * (sl t + 3)‖ * (((6 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 3)
      / (720 * (1 / 2 + 3)) ≤ C * (1000 / 1333039680) := by
    have := mul_le_mul hs4 h6 (by positivity) hC
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have kb : (1 / 2 + b) / 10 ^ 6 + (1 / 2 + b) / 10 ^ 6 / 12
      + (1 / 2 + b) * (3 / 2 + b) * (5 / 2 + b) / 10 ^ 6 / 720 ≤ 1 / 40000 := by
    have : (1 / 2 + b) * (3 / 2 + b) * (5 / 2 + b) ≤ (29 / 2) * (31 / 2) * (33 / 2) := by
      gcongr <;> linarith
    nlinarith
  linarith

/-! ## Enclosures of `log n` and `n^(-1/2)` -/

lemma log_two_bd : |Real.log 2 - 6931471805599 / 10 ^ 13| ≤ 4 / 10 ^ 10 := by
  have := Real.log_two_near_10
  rw [abs_le] at *; constructor <;> norm_num at * <;> linarith

lemma log_four_bd : |Real.log 4 - 13862943611199 / 10 ^ 13| ≤ 4 / 10 ^ 10 := by
  have := Real.log_two_near_10
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [e]; rw [abs_le] at *; constructor <;> norm_num at * <;> linarith

lemma log_three_bd : |Real.log 3 - 10986122886681 / 10 ^ 13| ≤ 4 / 10 ^ 10 := by
  have h2 := Real.log_two_near_10
  have h := Real.abs_log_sub_add_sum_range_le (show |(1/3:ℝ)| < 1 by norm_num) 22
  have e : Real.log (1 - 1/3) = Real.log 2 - Real.log 3 := by
    rw [show (1:ℝ) - 1/3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  rw [abs_le] at *; constructor <;> norm_num at * <;> linarith

lemma log_five_bd : |Real.log 5 - 16094379124341 / 10 ^ 13| ≤ 4 / 10 ^ 10 := by
  have h2 := Real.log_two_near_10
  have h := Real.abs_log_sub_add_sum_range_le (show |(1/5:ℝ)| < 1 by norm_num) 16
  have e : Real.log (1 - 1/5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1:ℝ) - 1/5 = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  rw [abs_le] at *; constructor <;> norm_num at * <;> linarith

lemma log_six_bd : |Real.log 6 - 17917594692281 / 10 ^ 13| ≤ 4 / 10 ^ 10 := by
  have h2 := Real.log_two_near_10
  have h := Real.abs_log_sub_add_sum_range_le (show |(1/3:ℝ)| < 1 by norm_num) 22
  have e : Real.log (1 - 1/3) = Real.log 2 - Real.log 3 := by
    rw [show (1:ℝ) - 1/3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e] at h
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ] at h
  rw [e6]; rw [abs_le] at *; constructor <;> norm_num at * <;> linarith

lemma rho2_bd : 7071067811865 / 10 ^ 13 ≤ rho 2 ∧ rho 2 ≤ 7071067811866 / 10 ^ 13 :=
  rho_bounds 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma rho3_bd : 5773502691896 / 10 ^ 13 ≤ rho 3 ∧ rho 3 ≤ 5773502691897 / 10 ^ 13 :=
  rho_bounds 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma rho4_bd : 5000000000000 / 10 ^ 13 ≤ rho 4 ∧ rho 4 ≤ 5000000000001 / 10 ^ 13 :=
  rho_bounds 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma rho5_bd : 4472135954999 / 10 ^ 13 ≤ rho 5 ∧ rho 5 ≤ 4472135955000 / 10 ^ 13 :=
  rho_bounds 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma rho6_bd : 4082482904638 / 10 ^ 13 ≤ rho 6 ∧ rho 6 ≤ 4082482904639 / 10 ^ 13 :=
  rho_bounds 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


/-! ## A Lipschitz bound for the approximant -/

lemma hasDerivAt_sl (t : ℝ) : HasDerivAt sl I t := by
  have h := ((hasDerivAt_id t).ofReal_comp).mul_const I
  have h2 := h.const_add (1 / 2 : ℂ)
  convert h2 using 1
  · funext x; simp [sl]
  · simp

lemma hasDerivAt_ex (n : ℕ) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (ex n) (ex n t * (-I * Real.log n)) t := by
  have e : ex n = fun t => cexp (-(sl t) * (Real.log n : ℂ)) := funext (ex_eq n hn)
  have h := ((hasDerivAt_sl t).neg.mul_const (Real.log n : ℂ)).cexp
  rw [e]
  convert h using 1
  try ring

lemma hasDerivAt_Qf {s : ℂ} (hs : s ≠ 1) : HasDerivAt Qf (Qd s) s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hi := ((hasDerivAt_id' s).sub_const 1).inv hs'
  have hp := (((hasDerivAt_id' s).mul ((hasDerivAt_id' s).add_const 1)).mul
    ((hasDerivAt_id' s).add_const 2))
  have h := (((hi.const_mul 6).const_add (1 / 2)).add ((hasDerivAt_id' s).div_const 72)).sub
    (hp.div_const 155520)
  have e : Qf = fun z => 1 / 2 + 6 * (z - 1)⁻¹ + z / 72 - z * (z + 1) * (z + 2) / 155520 := by
    funext z; simp only [Qf, div_eq_mul_inv]
  rw [e]
  convert h using 1
  simp only [Qd, Pi.mul_apply]
  field_simp
  ring

noncomputable def Azd (t : ℝ) : ℂ :=
  ex 2 t * (-I * Real.log 2) + ex 3 t * (-I * Real.log 3) + ex 4 t * (-I * Real.log 4)
    + ex 5 t * (-I * Real.log 5)
    + (ex 6 t * (-I * Real.log 6) * Qf (sl t) + ex 6 t * (Qd (sl t) * I))

lemma hasDerivAt_Az (t : ℝ) : HasDerivAt Az (Azd t) t := by
  have hQ : HasDerivAt (fun t => Qf (sl t)) (Qd (sl t) * I) t :=
    (hasDerivAt_Qf (sl_ne_one t)).comp t (hasDerivAt_sl t)
  have h := ((((((hasDerivAt_ex 2 (by norm_num) t).const_add 1).add (hasDerivAt_ex 3 (by norm_num) t)).add
    (hasDerivAt_ex 4 (by norm_num) t)).add (hasDerivAt_ex 5 (by norm_num) t)).add
    ((hasDerivAt_ex 6 (by norm_num) t).mul hQ))
  convert h using 1
  · funext u; simp only [Az, Pi.add_apply, Pi.mul_apply]
  · simp only [Azd]; push_cast; ring

noncomputable def BQ (lam m : ℝ) : ℝ := 1 / 2 + 6 / lam + m / 72 + m * (m + 1) * (m + 2) / 155520
noncomputable def BQd (lam m : ℝ) : ℝ := 6 / lam ^ 2 + 1 / 72 + (3 * m ^ 2 + 6 * m + 2) / 155520

/-- The Lipschitz constant, with the rational upper bounds of `rho n` and `log n`. -/
noncomputable def Lrat (lam m : ℝ) : ℝ :=
  7071067811866 / 10 ^ 13 * (6931471805599 / 10 ^ 13 + 4 / 10 ^ 10)
  + 5773502691897 / 10 ^ 13 * (10986122886681 / 10 ^ 13 + 4 / 10 ^ 10)
  + 5000000000001 / 10 ^ 13 * (13862943611199 / 10 ^ 13 + 4 / 10 ^ 10)
  + 4472135955000 / 10 ^ 13 * (16094379124341 / 10 ^ 13 + 4 / 10 ^ 10)
  + 4082482904639 / 10 ^ 13 * ((17917594692281 / 10 ^ 13 + 4 / 10 ^ 10) * BQ lam m + BQd lam m)

lemma log_le_of_bd {n : ℕ} {L : ℝ} (h : |Real.log n - L| ≤ 4 / 10 ^ 10) :
    Real.log n ≤ L + 4 / 10 ^ 10 := by
  rw [abs_le] at h; linarith

lemma norm_sl_sub_one_ge {a t lam : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) : lam ≤ ‖sl t - 1‖ := by
  have e : ‖sl t - 1‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [sl]; ring
  have : lam ^ 2 ≤ ‖sl t - 1‖ ^ 2 := by rw [e]; nlinarith
  nlinarith [norm_nonneg (sl t - 1)]

lemma norm_Qf_le {a t lam m : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) (hm : 1 / 2 + t ≤ m) : ‖Qf (sl t)‖ ≤ BQ lam m := by
  have hl := norm_sl_sub_one_ge ha hat hlam hlam2
  have ht0 : 0 ≤ t := ha.trans hat
  have hsj : ∀ j : ℝ, 0 ≤ j → ‖sl t + j‖ ≤ j + m := fun j hj => by
    have := norm_sl_add_le t j hj; rw [abs_of_nonneg ht0] at this; linarith
  have h0 := hsj 0 le_rfl; have h1 := hsj 1 (by norm_num); have h2 := hsj 2 (by norm_num)
  push_cast at h0 h1 h2; simp only [add_zero, zero_add] at h0
  have hm0 : 0 ≤ m := by linarith
  unfold Qf BQ
  have t1 : ‖(6 : ℂ) / (sl t - 1)‖ ≤ 6 / lam := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) hlam hl
  have t2 : ‖sl t / 72‖ ≤ m / 72 := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have t3 : ‖sl t * (sl t + 1) * (sl t + 2) / 155520‖ ≤ m * (m + 1) * (m + 2) / 155520 := by
    rw [norm_div, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    have := mul_le_mul (mul_le_mul h0 h1 (norm_nonneg _) hm0) h2 (norm_nonneg _) (by positivity)
    linarith
  have t0 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  calc _ ≤ ‖(1 / 2 : ℂ) + 6 / (sl t - 1) + sl t / 72‖ + ‖sl t * (sl t + 1) * (sl t + 2) / 155520‖ :=
        norm_sub_le _ _
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖(6 : ℂ) / (sl t - 1)‖ + ‖sl t / 72‖ + ‖sl t * (sl t + 1) * (sl t + 2) / 155520‖ := by
        have := norm_add_le ((1 / 2 : ℂ) + 6 / (sl t - 1)) (sl t / 72)
        have := norm_add_le (1 / 2 : ℂ) (6 / (sl t - 1))
        linarith
    _ ≤ _ := by linarith

lemma norm_Qd_le {a t lam m : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) (hm : 1 / 2 + t ≤ m) : ‖Qd (sl t)‖ ≤ BQd lam m := by
  have hl := norm_sl_sub_one_ge ha hat hlam hlam2
  have ht0 : 0 ≤ t := ha.trans hat
  have h0 : ‖sl t‖ ≤ m := by
    have := norm_sl_add_le t 0 le_rfl; rw [abs_of_nonneg ht0] at this; simp at this; linarith
  have hm0 : 0 ≤ m := by linarith
  unfold Qd BQd
  have t1 : ‖(-6 : ℂ) / (sl t - 1) ^ 2‖ ≤ 6 / lam ^ 2 := by
    rw [norm_div, norm_pow, norm_neg]; simp only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlam.le hl 2)
  have t3 : ‖(3 * sl t ^ 2 + 6 * sl t + 2) / 155520‖ ≤ (3 * m ^ 2 + 6 * m + 2) / 155520 := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    have : ‖3 * sl t ^ 2 + 6 * sl t + 2‖ ≤ 3 * m ^ 2 + 6 * m + 2 := by
      refine (norm_add_le _ _).trans ?_
      have := norm_add_le (3 * sl t ^ 2) (6 * sl t)
      rw [norm_mul, norm_mul, norm_pow] at this
      simp only [Complex.norm_ofNat] at this
      have : ‖sl t‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
      simp only [Complex.norm_ofNat]
      nlinarith
    linarith
  have t2 : ‖(1 / 72 : ℂ)‖ = 1 / 72 := by norm_num
  calc _ ≤ ‖(-6 : ℂ) / (sl t - 1) ^ 2 + 1 / 72‖ + ‖(3 * sl t ^ 2 + 6 * sl t + 2) / 155520‖ :=
        norm_sub_le _ _
    _ ≤ _ := by have := norm_add_le ((-6 : ℂ) / (sl t - 1) ^ 2) (1 / 72); linarith

lemma rho_nonneg (n : ℕ) : 0 ≤ rho n := (Real.exp_pos _).le

lemma norm_ex_mul_le (n : ℕ) (hn : 1 < n) (t q L : ℝ) (hq : rho n ≤ q)
    (hL : Real.log n ≤ L) : ‖ex n t * (-I * Real.log n)‖ ≤ q * L := by
  rw [norm_mul, norm_ex n (by omega), norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn.le))]
  exact mul_le_mul hq hL (Real.log_nonneg (by exact_mod_cast hn.le)) ((rho_nonneg n).trans hq)

theorem norm_Azd_le {a t lam m : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) (hm : 1 / 2 + t ≤ m) : ‖Azd t‖ ≤ Lrat lam m := by
  have e2 := norm_ex_mul_le 2 (by norm_num) t _ _ rho2_bd.2 (log_le_of_bd log_two_bd)
  have e3 := norm_ex_mul_le 3 (by norm_num) t _ _ rho3_bd.2 (log_le_of_bd log_three_bd)
  have e4 := norm_ex_mul_le 4 (by norm_num) t _ _ rho4_bd.2 (log_le_of_bd log_four_bd)
  have e5 := norm_ex_mul_le 5 (by norm_num) t _ _ rho5_bd.2 (log_le_of_bd log_five_bd)
  have e6 := norm_ex_mul_le 6 (by norm_num) t _ _ rho6_bd.2 (log_le_of_bd log_six_bd)
  have hQ := norm_Qf_le ha hat hlam hlam2 hm
  have hQd := norm_Qd_le ha hat hlam hlam2 hm
  have hBQ : 0 ≤ BQ lam m := (norm_nonneg _).trans hQ
  have hBQd : 0 ≤ BQd lam m := (norm_nonneg _).trans hQd
  have f1 : ‖ex 6 t * (-I * Real.log 6) * Qf (sl t)‖ ≤
      4082482904639 / 10 ^ 13 * (17917594692281 / 10 ^ 13 + 4 / 10 ^ 10) * BQ lam m := by
    rw [norm_mul]; exact mul_le_mul e6 hQ (norm_nonneg _) (by positivity)
  have f2 : ‖ex 6 t * (Qd (sl t) * I)‖ ≤ 4082482904639 / 10 ^ 13 * BQd lam m := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_ex 6 (by norm_num)]
    exact mul_le_mul rho6_bd.2 hQd (norm_nonneg _) (by positivity)
  unfold Azd Lrat
  have := norm_add_le (ex 6 t * (-I * Real.log 6) * Qf (sl t)) (ex 6 t * (Qd (sl t) * I))
  have := norm_add_le (ex 2 t * (-I * Real.log 2) + ex 3 t * (-I * Real.log 3) + ex 4 t * (-I * Real.log 4)
    + ex 5 t * (-I * Real.log 5)) (ex 6 t * (-I * Real.log 6) * Qf (sl t) + ex 6 t * (Qd (sl t) * I))
  have := norm_add_le (ex 2 t * (-I * Real.log 2) + ex 3 t * (-I * Real.log 3) + ex 4 t * (-I * Real.log 4))
    (ex 5 t * (-I * Real.log 5))
  have := norm_add_le (ex 2 t * (-I * Real.log 2) + ex 3 t * (-I * Real.log 3)) (ex 4 t * (-I * Real.log 4))
  have := norm_add_le (ex 2 t * (-I * Real.log 2)) (ex 3 t * (-I * Real.log 3))
  nlinarith

theorem Az_lip {a b t u lam : ℝ} (ha : 0 ≤ a) (ht : t ∈ Set.Icc a b) (hu : u ∈ Set.Icc a b)
    (hlam : 0 < lam) (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) :
    ‖Az t - Az u‖ ≤ Lrat lam (1 / 2 + b) * |t - u| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Az) (f' := Azd)
    (s := Set.Icc a b) (x := u) (y := t)
    (fun x _ => (hasDerivAt_Az x).hasDerivWithinAt)
    (fun x hx => norm_Azd_le (m := 1 / 2 + b) ha hx.1 hlam hlam2 (by linarith [hx.2])) (convex_Icc a b) hu ht
  simpa [Real.norm_eq_abs] using this


/-! ## Certified evaluation of the approximant at a point -/

/-- Iterated squaring. -/
def sqi : ℕ → ℂ → ℂ
  | 0, z => z
  | j + 1, z => sqi j z ^ 2

lemma sqi_exp (j : ℕ) (φ : ℝ) : sqi j (cexp (I * φ)) = cexp (I * ((2 ^ j * φ : ℝ) : ℂ)) := by
  induction j with
  | zero => simp [sqi]
  | succ j ih =>
    rw [sqi, ih, ← Complex.exp_natCast_mul]
    congr 1; push_cast; ring

lemma ball_sqi {j : ℕ} {z : ℂ} {a b r a' b' r' : ℝ} (h : ‖sqi j z - ⟨a, b⟩‖ ≤ r)
    (hc : |a * a - b * b - a'| + |2 * a * b - b'| + r * (2 * (|a| + |b|) + r) ≤ r') :
    ‖sqi (j + 1) z - ⟨a', b'⟩‖ ≤ r' := ball_sq h hc

lemma taylor_ball_r {φ a' b' r' : ℝ} (hφ : |φ| ≤ 1)
    (hc : |Pc φ - a'| + |Ps φ - b'| + |φ| ^ 12 * (13 / 5748019200) ≤ r') :
    ‖sqi 0 (cexp (I * φ)) - ⟨a', b'⟩‖ ≤ r' := ball_round (taylor_ball hφ) hc

lemma norm_exp_I_sub_le (x y : ℝ) : ‖cexp (I * x) - cexp (I * y)‖ ≤ |x - y| := by
  have : cexp (I * x) - cexp (I * y) = cexp (I * y) * (cexp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

/-- From a squaring chain for `exp(i φ)` to a ball for `ex n tk = n^(-1/2 - i tk)`. -/
lemma ex_ball {n : ℕ} (hn : 0 < n) (m : ℕ) {tk Lc φ a b r p q A B R η : ℝ}
    (hlog : |Real.log n - Lc| ≤ 4 / 10 ^ 10) (hρ : p ≤ rho n ∧ rho n ≤ q) (hp : 0 ≤ p)
    (htk : 0 ≤ tk) (hch : ‖sqi m (cexp (I * φ)) - ⟨a, b⟩‖ ≤ r)
    (hφ : |tk * Lc + 2 ^ m * φ| ≤ η)
    (hc : (q - p) + q * (r + η + tk * (4 / 10 ^ 10)) + |p * a - A| + |p * b - B| ≤ R) :
    ‖ex n tk - ⟨A, B⟩‖ ≤ R := by
  rw [sqi_exp] at hch
  set z := cexp (I * ((-(tk * Real.log n) : ℝ) : ℂ)) with hz
  have hz1 : ‖z‖ = 1 := norm_exp_I_mul_ofReal _
  have hd : |-(tk * Real.log n) - 2 ^ m * φ| ≤ η + tk * (4 / 10 ^ 10) := by
    have e : -(tk * Real.log n) - 2 ^ m * φ = -(tk * (Real.log n - Lc)) - (tk * Lc + 2 ^ m * φ) := by ring
    rw [e]
    have h1 : |tk * (Real.log n - Lc)| ≤ tk * (4 / 10 ^ 10) := by
      rw [abs_mul, abs_of_nonneg htk]; exact mul_le_mul_of_nonneg_left hlog htk
    have := abs_sub (-(tk * (Real.log n - Lc))) (tk * Lc + 2 ^ m * φ)
    rw [abs_neg] at this
    linarith
  have hzc : ‖z - ⟨a, b⟩‖ ≤ r + η + tk * (4 / 10 ^ 10) := by
    have := norm_exp_I_sub_le (-(tk * Real.log n)) (2 ^ m * φ)
    have h3 := norm_sub_le_norm_sub_add_norm_sub z (cexp (I * ((2 ^ m * φ : ℝ) : ℂ))) ⟨a, b⟩
    linarith
  have hr0 : 0 ≤ r + η + tk * (4 / 10 ^ 10) := (norm_nonneg _).trans hzc
  rw [ex_split n hn, ← hz]
  have e : (rho n : ℂ) * z - ⟨A, B⟩ = ((rho n - p : ℝ) : ℂ) * z + (p : ℂ) * (z - ⟨a, b⟩)
      + ⟨p * a - A, p * b - B⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [e]
  have t1 : ‖((rho n - p : ℝ) : ℂ) * z‖ ≤ q - p := by
    rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.1])]
    linarith [hρ.2]
  have t2 : ‖(p : ℂ) * (z - ⟨a, b⟩)‖ ≤ q * (r + η + tk * (4 / 10 ^ 10)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul (by linarith [hρ.1, hρ.2]) hzc (norm_nonneg _) (hp.trans (hρ.1.trans hρ.2))
  have t3 := norm_mk_le (p * a - A) (p * b - B)
  have := norm_add_le (((rho n - p : ℝ) : ℂ) * z + (p : ℂ) * (z - ⟨a, b⟩)) ⟨p * a - A, p * b - B⟩
  have := norm_add_le (((rho n - p : ℝ) : ℂ) * z) ((p : ℂ) * (z - ⟨a, b⟩))
  linarith

/-- Combining the five balls into a ball for `Az tk`. -/
lemma Az_ball {tk a2 b2 r2 a3 b3 r3 a4 b4 r4 a5 b5 r5 a6 b6 r6 cr ci R : ℝ}
    (h2 : ‖ex 2 tk - ⟨a2, b2⟩‖ ≤ r2) (h3 : ‖ex 3 tk - ⟨a3, b3⟩‖ ≤ r3)
    (h4 : ‖ex 4 tk - ⟨a4, b4⟩‖ ≤ r4) (h5 : ‖ex 5 tk - ⟨a5, b5⟩‖ ≤ r5)
    (h6 : ‖ex 6 tk - ⟨a6, b6⟩‖ ≤ r6)
    (hc : |1 + a2 + a3 + a4 + a5 + (a6 * Qre tk - b6 * Qim tk) - cr|
      + |b2 + b3 + b4 + b5 + (a6 * Qim tk + b6 * Qre tk) - ci|
      + (r2 + r3 + r4 + r5 + r6 * (|Qre tk| + |Qim tk|)) ≤ R) :
    ‖Az tk - ⟨cr, ci⟩‖ ≤ R := by
  have hQ := norm_mk_le (Qre tk) (Qim tk)
  have h6' : ‖ex 6 tk * Qf (sl tk) - ⟨a6 * Qre tk - b6 * Qim tk, a6 * Qim tk + b6 * Qre tk⟩‖
      ≤ r6 * (|Qre tk| + |Qim tk|) := by
    have e : ex 6 tk * Qf (sl tk) - ⟨a6 * Qre tk - b6 * Qim tk, a6 * Qim tk + b6 * Qre tk⟩
        = (ex 6 tk - ⟨a6, b6⟩) * ⟨Qre tk, Qim tk⟩ := by
      rw [Qf_sl]; apply Complex.ext <;> simp <;> ring
    rw [e, norm_mul]
    exact mul_le_mul h6 hQ (norm_nonneg _) ((norm_nonneg _).trans h6)
  have e : Az tk - ⟨1 + a2 + a3 + a4 + a5 + (a6 * Qre tk - b6 * Qim tk),
      b2 + b3 + b4 + b5 + (a6 * Qim tk + b6 * Qre tk)⟩
      = (ex 2 tk - ⟨a2, b2⟩) + (ex 3 tk - ⟨a3, b3⟩) + (ex 4 tk - ⟨a4, b4⟩) + (ex 5 tk - ⟨a5, b5⟩)
        + (ex 6 tk * Qf (sl tk) - ⟨a6 * Qre tk - b6 * Qim tk, a6 * Qim tk + b6 * Qre tk⟩) := by
    rw [Az]; apply Complex.ext <;> simp <;> ring
  have hb : ‖Az tk - ⟨1 + a2 + a3 + a4 + a5 + (a6 * Qre tk - b6 * Qim tk),
      b2 + b3 + b4 + b5 + (a6 * Qim tk + b6 * Qre tk)⟩‖
      ≤ r2 + r3 + r4 + r5 + r6 * (|Qre tk| + |Qim tk|) := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le ((ex 2 tk - ⟨a2, b2⟩) + (ex 3 tk - ⟨a3, b3⟩) + (ex 4 tk - ⟨a4, b4⟩))
      (ex 5 tk - ⟨a5, b5⟩)
    have := norm_add_le ((ex 2 tk - ⟨a2, b2⟩) + (ex 3 tk - ⟨a3, b3⟩)) (ex 4 tk - ⟨a4, b4⟩)
    have := norm_add_le (ex 2 tk - ⟨a2, b2⟩) (ex 3 tk - ⟨a3, b3⟩)
    linarith
  exact ball_round hb (by linarith)

/-! ## The certificate for one interval -/

theorem pt_cert {a b tk lam C w cr ci R lo : ℝ} (ha : 0 ≤ a) (hak : a ≤ tk) (hkb : tk ≤ b)
    (hb : b ≤ 14) (hw1 : tk - a ≤ w) (hw2 : b - tk ≤ w) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ 1 / 4 + a ^ 2) (hC : 0 ≤ C)
    (hCb : (1 / 4 + b ^ 2) * (9 / 4 + b ^ 2) * (25 / 4 + b ^ 2) * (49 / 4 + b ^ 2) ≤ C ^ 2)
    (hball : ‖Az tk - ⟨cr, ci⟩‖ ≤ R) (hlo : 0 ≤ lo) (hsq : (lo + R) ^ 2 ≤ cr ^ 2 + ci ^ 2)
    (hm : C * (1000 / 1333039680) + 1 / 40000 + Lrat lam (1 / 2 + b) * w < lo) :
    ∀ t ∈ Set.Icc a b, riemannZeta (sl t) ≠ 0 := by
  intro t ht hz
  have hR : 0 ≤ R := (norm_nonneg _).trans hball
  have hc : lo + R ≤ ‖(⟨cr, ci⟩ : ℂ)‖ := by
    have e : ‖(⟨cr, ci⟩ : ℂ)‖ ^ 2 = cr ^ 2 + ci ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg (⟨cr, ci⟩ : ℂ)]
  have hk : lo ≤ ‖Az tk‖ := by
    have := norm_sub_norm_le (⟨cr, ci⟩ : ℂ) (Az tk)
    rw [norm_sub_rev] at this; linarith
  have hL := Az_lip ha ht ⟨hak, hkb⟩ hlam hlam2
  have hLn : 0 ≤ Lrat lam (1 / 2 + b) := by
    unfold Lrat BQ BQd; have : 0 ≤ b := ha.trans (hak.trans hkb); positivity
  have hw : |t - tk| ≤ w := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hL' : ‖Az t - Az tk‖ ≤ Lrat lam (1 / 2 + b) * w :=
    hL.trans (mul_le_mul_of_nonneg_left hw hLn)
  have hE := norm_zeta_sub_Az_le (ha.trans ht.1) ht.2 hb hC hCb
  rw [hz, zero_sub, norm_neg] at hE
  have := norm_sub_norm_le (Az tk) (Az t)
  rw [norm_sub_rev] at hL'
  linarith

lemma cover {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ t ∈ Set.Icc a b, P t)
    (h2 : ∀ t ∈ Set.Icc b c, P t) : ∀ t ∈ Set.Icc a c, P t := fun t ht => by
  by_cases h : t ≤ b
  · exact h1 t ⟨ht.1, h⟩
  · exact h2 t ⟨(not_le.mp h).le, ht.2⟩

end SchoenfeldS1.Z

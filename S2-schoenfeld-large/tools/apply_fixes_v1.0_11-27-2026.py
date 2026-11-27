"""Copy the stripped closure (stripped/) to src/ with the fixes for Lean v4.37.0-rc1 / Mathlib 31ce06ea.
usage: python3 -I apply_fixes_v1.0_11-27-2026.py PORT_DIR
Writes a file only when its content changes, so make rebuilds only what changed."""
import os, re, sys
PORT = sys.argv[1]
RAW, SRC = os.path.join(PORT, 'stripped'), os.path.join(PORT, 'src')
SP = 'SchoenfeldPort/'

# Global renames (regex, replacement): Mathlib name changes between v4.35.0-rc3 and 31ce06ea.
GLOBAL = [
    # Continuous.div now concludes `Continuous (f / g)`; the pointwise form is `div₀`
    (r'\b(Continuous|continuous_const|ContinuousAt|ContinuousOn)\.div ', r'\1.div₀ '),
    (r'\bintegral_finset_sum', 'integral_finsetSum'),
    # likewise `X.div` now concludes `X (f / g)`; the pointwise form is `X.fun_div`
    (r'\b(DifferentiableAt|DifferentiableOn|Differentiable|HasDerivAt|HasDerivWithinAt|'
     r'DifferentiableWithinAt|AnalyticAt|MeromorphicAt)\.div\b', r'\1.fun_div'),
    (r'\bintegrable_finset_sum', 'integrable_finsetSum'),
]

# Per-file exact replacements (file, old, new).
LOCAL = [
    ('PNTPort/ExplicitPsi1/Merom.lean', 'MeromorphicAt.const 1 p', 'MeromorphicAt.const (1 : ℂ) p'),
    ('PNTPort/ExplicitPsi1/Merom.lean',
     'rw [meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_zeta p) h',
     'rw [meromorphicOrderAt_logDeriv_eq_neg_one h'),
    ('PNTPort/StrongPNT/EulerMaclaurin.lean',
     'apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)',
     'apply MeasureTheory.Measure.integrableOn_of_bounded (by simp)\n'
     '    (by apply Measurable.aestronglyMeasurable; unfold B1; fun_prop) (M := 1 / 2)'),
    ('ChebyshevExplicit/Psi30Upper.lean',
     '      have := Real.exp_nat_mul 1 3\n      rw [mul_one] at this\n'
     '      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, this]\n',
     '      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]\n'),
    # field_simp now leaves `I * t` against `t * I`; `congr 2` then times out
    ('PNTPort/ZetaZeros/Perron1.lean', '    congr 2; funext t; ring_nf\n', '    simp_rw [mul_comm I]\n'),
    ('PNTPort/StrongPNT/ResidueCalcOnRectangles.lean',
     '  exact (analyticAt_const.meromorphicAt.div\n    ((analyticAt_id.sub analyticAt_const).meromorphicAt))',
     '  exact (analyticAt_const (v := c p)).meromorphicAt.div\n'
     '    ((analyticAt_id.sub (analyticAt_const (v := p))).meromorphicAt)'),
    ('PNTPort/StrongPNT/ZetaBounds.lean', '    exact (xpos_of_uIcc ha hx).ne\'\n  · norm_cast; ring_nf\n',
     '    exact (xpos_of_uIcc ha hx).ne\'\n  · simp only [Complex.ofReal_natCast, neg_add_eq_sub]\n'),
    ('PNTPort/StrongPNT/ZetaBounds.lean',
     '  refine IsOpen.inter isOpen_ne ?_\n  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)',
     '  have h : IsOpen ({z : ℂ | z ≠ 1} ∩ {z : ℂ | 0 < z.re}) :=\n'
     '    IsOpen.inter isOpen_ne (isOpen_lt continuous_const Complex.continuous_re)\n  exact h'),
    ('PNTPort/StrongPNT/ZetaBounds.lean', '(by simp only [Nat.one_le_cast]; omega)', '(show (1 : ℝ) ≤ N by exact_mod_cast Npos)'),
    ('PNTPort/StrongPNT/ZetaBounds.lean', """  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
""", """  simp_rw [div_eq_mul_inv]
  have h1 : HasDerivAt (fun z ↦ - (N : ℂ) ^ z) (- (N : ℂ) ^ z * Real.log N) z := by
    simp only [natCast_log, neg_mul]
    apply HasDerivAt.fun_neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  have h2 : HasDerivAt (fun z : ℂ ↦ z⁻¹) (- (z ^ 2)⁻¹) z := hasDerivAt_inv z_ne_zero
  convert! h1.fun_mul h2 using 1
  simp only [natCast_log, neg_mul, mul_neg, neg_neg]
  ring_nf
"""),
    ('PNTPort/StrongPNT/StrongPNT.lean', '      (AnalyticOnNhd.sub analyticOnNhd_const\n',
     '      (AnalyticOnNhd.fun_sub analyticOnNhd_const\n'),
    ('PNTPort/StrongPNT/StrongPNT.lean',
     '      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith\n',
     '      · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Mpos.le) (by linarith)) (by linarith)\n'),
    ('PNTPort/ZetaZeros/Sym.lean',
     'lemma strip_open : IsOpen strip :=\n  (isOpen_lt continuous_const Complex.continuous_re).inter\n'
     '    (isOpen_lt Complex.continuous_re continuous_const)\n',
     'lemma strip_open : IsOpen strip := by\n'
     '  have h : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}) :=\n'
     '    (isOpen_lt continuous_const Complex.continuous_re).inter\n'
     '      (isOpen_lt Complex.continuous_re continuous_const)\n  exact h\n'),
]

done = set()
for root, _, fs in os.walk(RAW):
    for f in fs:
        rel = os.path.relpath(os.path.join(root, f), RAW)
        s = open(os.path.join(root, f)).read()
        for a, b in GLOBAL:
            s = re.sub(a, b, s)
        if rel == SP + 'PNTPort/StrongPNT/StrongPNT.lean':
            # `open Nat` makes the bare name ambiguous with Nat.dist_zero_right
            s = re.sub(r'(?<![\w.])dist_zero_right', '_root_.dist_zero_right', s)
        for (lf, old, new) in LOCAL:
            if rel == SP + lf:
                if old not in s:
                    sys.exit('fix not applicable: %s: %r' % (lf, old[:60]))
                s = s.replace(old, new)
                done.add((lf, old))
        dst = os.path.join(SRC, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if not os.path.exists(dst) or open(dst).read() != s:
            open(dst, 'w').write(s)
            print('updated', rel)
missing = [x for x in LOCAL if (x[0], x[1]) not in done]
if missing:
    sys.exit('fixes for missing files: %r' % [m[0] for m in missing])

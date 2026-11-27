#!/usr/bin/env python3
"""Generator for the S1Z grid certificates (zeta(1/2+it) != 0 for 0 <= t <= 14).
Emits Lean modules S1ZG<k>_v1.0_11-27-2026.lean, each proving `iv_<i>` lemmas
`forall t in Icc a b, riemannZeta (sl t) != 0` from SchoenfeldS1.ZCore, plus S1ZGrid (the cover).
Exact rational arithmetic (fractions.Fraction); floats only to choose the grid.
AI-written (Claude), 11-27-2026, Apache-2.0."""
import sys, math
from fractions import Fraction as F

D = 10**15
T13 = 10**13
LC = {2: 6931471805599, 3: 10986122886681, 4: 13862943611199, 5: 16094379124341, 6: 17917594692281}
RHO = {2: (7071067811865, 7071067811866), 3: (5773502691896, 5773502691897), 4: (5000000000000, 5000000000001),
       5: (4472135954999, 4472135955000), 6: (4082482904638, 4082482904639)}
LOGBD = {2: 'log_two_bd', 3: 'log_three_bd', 4: 'log_four_bd', 5: 'log_five_bd', 6: 'log_six_bd'}
DELTA = F(4, 10**10)

def rnd(x):  # nearest with denominator D
    return F(round(x * D), D)
def up(x):   # rational >= x with denominator D
    return F(math.floor(x * D) + 1, D)
def lean(x):
    x = F(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"
def Pc(p): return 1 - p**2/2 + p**4/24 - p**6/720 + p**8/40320 - p**10/3628800
def Ps(p): return p - p**3/6 + p**5/120 - p**7/5040 + p**9/362880 - p**11/39916800
def Qre(t): return F(1,2) - 3/(F(1,4)+t**2) + F(1,144) - (F(15,8) - 9*t**2/2)/155520
def Qim(t): return -6*t/(F(1,4)+t**2) + t/72 - (23*t/4 - t**3)/155520
def BQ(lam, m): return F(1,2) + 6/lam + m/72 + m*(m+1)*(m+2)/155520
def BQd(lam, m): return 6/lam**2 + F(1,72) + (3*m**2+6*m+2)/155520
def Lrat(lam, m):
    s = sum(F(RHO[n][1], T13) * (F(LC[n], T13) + DELTA) for n in [2,3,4,5])
    return s + F(RHO[6][1], T13) * ((F(LC[6], T13) + DELTA) * BQ(lam, m) + BQd(lam, m))

def ex_chain(n, tk):
    """Returns (lean lines, A, B, R) for the ball of ex n tk."""
    Lc = F(LC[n], T13)
    th = tk * Lc
    m = 0
    while abs(th) / 2**m > F(1, 2):
        m += 1
    phi = rnd(-th / 2**m)
    eta = F(2**m, D)
    assert abs(tk*Lc + 2**m*phi) <= eta
    lines = []
    a, b = rnd(Pc(phi)), rnd(Ps(phi))
    r = up(abs(Pc(phi)-a) + abs(Ps(phi)-b) + abs(phi)**12 * F(13, 5748019200))
    lines.append(f"    have c0 := taylor_ball_r (φ := {lean(phi)}) (a' := {lean(a)}) (b' := {lean(b)}) (r' := {lean(r)}) (by norm_num) (by norm_num [Pc, Ps])")
    for j in range(1, m+1):
        a2, b2 = rnd(a*a - b*b), rnd(2*a*b)
        r2 = up(abs(a*a-b*b-a2) + abs(2*a*b-b2) + r*(2*(abs(a)+abs(b)) + r))
        lines.append(f"    have c{j} := ball_sqi (a' := {lean(a2)}) (b' := {lean(b2)}) (r' := {lean(r2)}) c{j-1} (by norm_num)")
        a, b, r = a2, b2, r2
    p, q = F(RHO[n][0], T13), F(RHO[n][1], T13)
    A, B = rnd(p*a), rnd(p*b)
    R = up((q-p) + q*(r + eta + tk*DELTA) + abs(p*a-A) + abs(p*b-B))
    lines.append(f"    exact ex_ball (A := {lean(A)}) (B := {lean(B)}) (R := {lean(R)}) (η := {lean(eta)}) (by norm_num) {m} {LOGBD[n]} rho{n}_bd (by norm_num) (by norm_num) c{m} (by norm_num) (by norm_num)")
    return lines, A, B, R

def Pb(b): return (F(1,4)+b**2)*(F(9,4)+b**2)*(F(25,4)+b**2)*(F(49,4)+b**2)

def cert(a, b):
    """Try to certify [a, b]. Returns (ok, lean text)."""
    tk = (a + b) / 2
    w = (b - a) / 2
    lam = F(math.floor(math.sqrt(float(F(1,4) + a*a)) * 10**6), 10**6)
    while lam**2 > F(1,4) + a*a: lam -= F(1, 10**6)
    C = F(math.ceil(math.sqrt(float(Pb(b))) * 10**3) + 1, 10**3)
    assert C**2 >= Pb(b)
    body = []
    balls = {}
    for n in [2,3,4,5,6]:
        lines, A, B, R = ex_chain(n, tk)
        body.append(f"  have h{n} : ‖ex {n} {lean(tk)} - ⟨{lean(A)}, {lean(B)}⟩‖ ≤ {lean(R)} := by")
        body += lines
        balls[n] = (A, B, R)
    qr, qi = Qre(tk), Qim(tk)
    a2,b2,r2 = balls[2]; a3,b3,r3 = balls[3]; a4,b4,r4 = balls[4]; a5,b5,r5 = balls[5]; a6,b6,r6 = balls[6]
    ecr = 1 + a2 + a3 + a4 + a5 + (a6*qr - b6*qi)
    eci = b2 + b3 + b4 + b5 + (a6*qi + b6*qr)
    cr, ci = rnd(ecr), rnd(eci)
    R = up(abs(ecr-cr) + abs(eci-ci) + (r2+r3+r4+r5 + r6*(abs(qr)+abs(qi))))
    nrm = math.sqrt(float(cr*cr + ci*ci))
    lo = F(math.floor((nrm - float(R)) * 10**6) - 1, 10**6)
    if lo < 0 or (lo + R)**2 > cr*cr + ci*ci:
        return False, None
    eps = C * F(1000, 1333039680) + F(1, 40000)
    marg = eps + Lrat(lam, F(1,2) + b) * w
    if not marg < lo:
        return False, float(lo - marg)
    body.append(f"  have hb := Az_ball (cr := {lean(cr)}) (ci := {lean(ci)}) (R := {lean(R)}) h2 h3 h4 h5 h6 (by norm_num [Qre, Qim])")
    body.append(f"  exact pt_cert (a := {lean(a)}) (b := {lean(b)}) (lam := {lean(lam)}) (C := {lean(C)}) (w := {lean(w)}) (lo := {lean(lo)})")
    body.append("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    body.append("    (by norm_num) (by norm_num) (by norm_num) hb (by norm_num) (by norm_num) (by norm_num [Lrat, BQ, BQd])")
    return True, body

def grid():
    # adaptive: grow interval greedily on a 1/1000 lattice, verify exactly
    ivs = []
    a = F(0)
    END = F(14)
    while a < END:
        # float guess of the allowed width from the true |A| (estimated by a coarse step)
        wtry = F(1, 1)
        while True:
            b = min(END, a + wtry)
            b = F(math.floor(b * 1000), 1000) if b < END else END
            if b <= a: b = a + F(1, 1000)
            ok, body = cert(a, b)
            if ok:
                ivs.append((a, b, body)); a = b; break
            wtry = wtry * F(3, 4)
            assert wtry > F(1, 10**5), ("stuck", float(a))
    return ivs

HEADER = """/-
Schoenfeld S1, part Z, generated grid module {k}: certified non-vanishing of zeta(1/2 + it)
on consecutive intervals. Generated by tools/s1z_gen_v1.0_11-27-2026.py (exact rational
arithmetic). AI-written Lean code (Claude), 11-27-2026, checked only by the Lean kernel; Mathlib,
Tau Ceti (Apache-2.0). Apache-2.0.
-/
import SchoenfeldS1.ZCore

namespace SchoenfeldS1.Z
open Complex

"""

def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    outdir = sys.argv[2] if len(sys.argv) > 2 else '.'
    ivs = grid()
    print("intervals:", len(ivs), file=sys.stderr)
    mods = [ivs[i:i+per] for i in range(0, len(ivs), per)]
    idx = 0
    names = []
    for k, mod in enumerate(mods):
        txt = HEADER.format(k=k)
        first = idx
        for (a, b, body) in mod:
            txt += f"theorem iv_{idx} : ∀ t ∈ Set.Icc {lean(a)} {lean(b)}, riemannZeta (sl t) ≠ 0 := by\n"
            txt += "\n".join(body) + "\n\n"
            idx += 1
        # module cover
        A0, B1 = mod[0][0], mod[-1][1]
        txt += f"theorem blk_{k} : ∀ t ∈ Set.Icc {lean(A0)} {lean(B1)}, riemannZeta (sl t) ≠ 0 :=\n  "
        expr = f"iv_{first}"
        for i in range(first+1, idx):
            expr = f"(cover {expr} iv_{i})"
        txt += expr + "\n\nend SchoenfeldS1.Z\n"
        open(f"{outdir}/S1ZG{k}_v1.0_11-27-2026.lean", 'w').write(txt)
        names.append((k, A0, B1))
    # grid cover module
    txt = """/-
Schoenfeld S1, part Z: the generated blocks joined, zeta(1/2 + it) != 0 for 0 <= t <= 14.
Generated by tools/s1z_gen_v1.0_11-27-2026.py. AI-written Lean code (Claude), 11-27-2026. Apache-2.0.
-/
""" + "".join(f"import SchoenfeldS1.ZG{k}\n" for k, _, _ in names) + """
namespace SchoenfeldS1.Z

theorem zeta_sl_ne_zero_of_le_fourteen : ∀ t ∈ Set.Icc (0 : ℝ) 14, riemannZeta (sl t) ≠ 0 :=
  """
    expr = "blk_0"
    for k, _, _ in names[1:]:
        expr = f"(cover {expr} blk_{k})"
    txt += expr + "\n\nend SchoenfeldS1.Z\n"
    open(f"{outdir}/S1ZGrid_v1.0_11-27-2026.lean", 'w').write(txt)
    for k, a, b in names: print(k, float(a), float(b), file=sys.stderr)

if __name__ == '__main__':
    main()

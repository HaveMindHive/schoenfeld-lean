# Schoenfeld S1, sub-project Z: `NT 14 = 0` (11-27-2026)

Status: **DONE.** `SchoenfeldS1.NT_fourteen_eq_zero : NT 14 = 0`, sorry-free, no `native_decide`,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (scratch/z/axioms-Z.txt). `NT` is the
S1A convention (zeros in the open strip, `0 < Im ρ ≤ T`, with multiplicity). RH (`riemannHypothesis`,
Levent Alpöge with Claude, module `Main` of the RH repository, imported through the port) is used
only for the reduction to the critical line.

## Files (module = `SchoenfeldS1.<name>`, built with tools/build1 into build/SchoenfeldS1/)

| file | content | build time |
|---|---|---|
| `S1ZCore_v1.0_11-27-2026.lean` | analysis + ball arithmetic + interval certificate | 8 s |
| `S1ZG0/1/2_v1.0_11-27-2026.lean` | 49 generated interval lemmas `iv_0..iv_48`, blocks `blk_0..2` | 10 to 15 s each (parallel) |
| `S1ZGrid_v1.0_11-27-2026.lean` | `zeta_sl_ne_zero_of_le_fourteen` (cover of [0,14]) | 2 s |
| `S1Z_v1.0_11-27-2026.lean` | RH reduction, `NT_fourteen_eq_zero`, `ordinates14` | 2 s |
| `tools/s1z_gen_v1.0_11-27-2026.py` | frozen generator (exact `Fraction` arithmetic) | 0.2 s |

Regenerate: `cd scratch/z/gen && python3 ../../../tools/s1z_gen_v1.0_11-27-2026.py 20 .`, copy
`S1ZG*`, `S1ZGrid` to the folder, `tools/build1_v1.0_11-27-2026.sh ZCore`, then `ZG0 ZG1 ZG2`, `ZGrid`, `Z`.
SHA-256: generator `1d0bf0dafba493953a7d1f3af29160375dab42ba942b70d76d5e0acdb9e9e9b7`;
ZG0 `79343af9...2569`, ZG1 `9ecccc6a...c56`, ZG2 `985430cf...baadd`, ZGrid `11a72930...463b`,
ZCore `320f93b1...27e`, Z `298acd8c...514b` (full hashes: `shasum -a 256 S1Z*.lean`).

## Proven (exact statements)

```
theorem SchoenfeldS1.NT_fourteen_eq_zero_of_line
    (h : ∀ t : ℝ, 0 < t → t ≤ 14 → riemannZeta (1 / 2 + t * I) ≠ 0) : NT 14 = 0      -- uses RH
theorem SchoenfeldS1.NT_fourteen_eq_zero : NT 14 = 0
theorem SchoenfeldS1.ordinates14 : Ordinates14 gZ                                     -- via S1A
theorem SchoenfeldS1.Z.zeta_sl_ne_zero_of_le_fourteen :
    ∀ t ∈ Set.Icc (0 : ℝ) 14, riemannZeta (sl t) ≠ 0        -- sl t = 1/2 + t I; no RH
theorem SchoenfeldS1.Z.norm_zeta_sub_AEM_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖ζ s - AEM N s‖ ≤ ‖s‖ M^(-σ)/(2σ) + ‖s‖ M^(-σ-1)/12 + ‖s(s+1)(s+2)‖ M^(-σ-3)/720
      + ‖s(s+1)(s+2)(s+3)‖ N^(-σ-3)/(720 (σ+3))
  -- AEM N s = Σ_{n≤N} n^-s - N^-s/2 + N^(1-s)/(s-1) + s N^(-s-1)/12 - s(s+1)(s+2) N^(-s-3)/720
theorem SchoenfeldS1.Z.norm_zeta_sub_Az_le (0 ≤ t ≤ b ≤ 14, C ≥ 0, C² ≥ Π_{j<4}((j+1/2)²+b²)) :
    ‖ζ(sl t) - Az t‖ ≤ C · 1000/1333039680 + 1/40000
theorem SchoenfeldS1.Z.Az_lip : ‖Az t - Az u‖ ≤ Lrat λ (1/2 + b) · |t - u|   (t,u ∈ [a,b], λ² ≤ 1/4 + a²)
theorem SchoenfeldS1.Z.pt_cert ...   -- one interval from rational inequalities
```

## Route and why

(a) Euler-Maclaurin, chosen. Tau Ceti has only the first-order zeta formula (error `|s| a^(-σ)/(2σ)`,
useless at `t = 14`) but also the general order-`k` Euler-Maclaurin formula. Order 4 is obtained
exactly without limits: Tau Ceti's first-order formula cut at `M = 10^12` plus the order-4 formula on
`[N, M]`; the `M` terms are bounded (`≤ 2.2e-5` total). With `N = 6` the remainder is `≤ 0.0304` at
`t = 14` (true `|ζ| = 0.1056` there) and needs only `|B₄({x})| ≤ 1/30` (`(x(1-x))² - 1/30`).
Instead of a Cauchy bound for `ζ'`, the Lipschitz step is on the explicit approximant
`Az t = 1 + 2^-s + 3^-s + 4^-s + 5^-s + 6^-s Q(s)` (mean value theorem, `‖Az'‖` bounded term by term,
`1/|s-1|` through a per-interval rational `λ`). Evaluation: `n^-s = n^(-1/2) exp(-i t log n)`, `log n`
from `Real.log_two_near_10` and the `log(1-x)` series (`x = 1/3, 1/5`), `exp(iφ)` by the degree-11
Taylor polynomial (`Complex.exp_bound`, `|φ| ≤ 1/2`) and up to 6 squarings, all as rational balls
(`‖z - ⟨a,b⟩‖ ≤ r`) checked by `norm_num`. (b) Riemann-Siegel remainders are not formalized anywhere
here; (c) argument-principle certificates (Tau Ceti `Certificate.lean`) are not built (Finding 5 of S1).

## Grid

49 intervals on `[0, 14]` (adaptive, endpoints on a `1/1000` lattice, centre `tk`, half-width `w`),
5 values `n = 2..6` per interval, 0 to 6 squarings each: about 1 400 `norm_num` side conditions.
Finest near `t = 14` (last interval widths about 0.03 to 0.06). Numeric sanity (scratch, not a proof):
the certified centres agree with mpmath `ζ(1/2 + i tk)` to about `1e-3`, within the proven `ε`.
The first zero near 14.13 is not used anywhere.

## Remaining

Nothing for (A). Not done: mirror to OneDrive (tools/mirror, left to the owner since another agent
shares the folder). The S1 PROGRESS file (other agent's) is not edited; its (A) line can now point
here.

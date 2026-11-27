# Schoenfeld port, progress (11-27-2026)

Stage S2: goldbach-lean's Schoenfeld-shape RH bounds, ported from Lean v4.35.0-rc3 to the
environment where RH is proven (riemann-hypothesis-community repo, Lean v4.37.0-rc1,
Mathlib 31ce06ea, Tau Ceti 2a9233e5). Source: goldbach-lean commit 05fe86a,
entries/goldbachintervalsrh445 (read-only). Neither upstream repo was modified.

## Status: COMPLETE

All 50 modules compile, with no sorry, admit or native_decide. Final.lean discharges the RH
hypothesis with `riemannHypothesis` from `Main`.

```
SchoenfeldPort.schoenfeld_psi_large (hZ : HSWN70 gZ ∧ HSWHead14 gZ ∧ Ordinates14 gZ) :
  ∀ x ≥ 10 ^ 11, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * Real.pi)
SchoenfeldPort.schoenfeld_theta_large (same hZ) :
  ∀ x ≥ 10 ^ 11, |Chebyshev.theta x - x| ≤ √x * Real.log x ^ 2 / (8 * Real.pi)
SchoenfeldPort.psi_sub_theta_large : ∀ x ≥ 10 ^ 11, ψ x - θ x ≤ 1.2 * √x
```
`#print axioms` on all three: [propext, Classical.choice, Quot.sound]
(final-check_v1.0_11-27-2026.txt).

## How it was built

1. `tools/strip_closure_v1.0_11-27-2026.py`: declaration-level dependency closure of
   psi_schoenfeld_large, theta_schoenfeld_large, psi_sub_theta_large (over-approximate name
   resolution: namespaces, opens, dot notation), writes the kept declarations to `stripped/`,
   renames LeanLab to SchoenfeldPort, removes module-system headers (plain files), replaces
   imports of dropped files by what they imported. Table: closure-table_v1.0_11-27-2026.txt.
2. `tools/apply_fixes_v1.0_11-27-2026.py`: copies `stripped/` to `src/` with the fixes below.
3. `tools/gen_makefile_v1.0_11-27-2026.py` then `make -C build -j6`: one olean per module, lean of
   the RH repo's toolchain, LEAN_PATH = build/ + the RH repo's built oleans. Nothing written there.
4. `tools/lean1_v1.0_11-27-2026.sh FILE`: check one file in that environment.
5. (local mirror script omitted from the public repo)

## Fixes for the newer Lean / Mathlib

* Mathlib now states `Continuous.div`, `DifferentiableAt.div`, `HasDerivAt.mul`, ... with the
  Pi operation (`f / g`); the pointwise forms are `div₀` (Continuous*) and `fun_div`, `fun_mul`,
  `fun_neg`, `fun_sub`. Renamed globally for explicit uses of `.div`; locally elsewhere. These
  caused the heartbeat timeouts in Perron1, ResidueCalcOnRectangles, ZetaBounds, StrongPNT.
* `integral_finset_sum` / `integrable_finset_sum` renamed to `...finsetSum`.
* `meromorphicOrderAt_logDeriv_eq_neg_one` lost its `MeromorphicAt` argument (Merom).
* `MeromorphicAt.const 1 p`, `analyticAt_const`: numeral types made explicit.
* `Real.exp_nat_mul` argument order changed (Psi30Upper); replaced by `Real.exp_one_pow`.
* `fun_prop` measurability of `B1` (EulerMaclaurin), `{z | P z ∧ Q z}` as an intersection
  (ZetaBounds, Sym), `field_simp` normal form (Perron1, ZetaBounds), `_root_.dist_zero_right`
  ambiguity with `Nat.dist_zero_right` under `open Nat` (StrongPNT), one `mul_nonneg` refine
  replaced by `div_nonneg` (StrongPNT).
* `Mathlib.Tactic.LinearCombinationPrime` no longer exists; the `additive_combination` tactic file
  (PNTPort/StrongPNT/Tactic/AdditiveCombination.lean) is used by no kept proof and is not ported.

## Source sorry

The one `sorry` hit in AdditiveCombination.lean is `Term.withoutErrToSorry`, a Lean
metaprogramming API name in the tactic's elaborator, not a proof gap. The file is not in the
closure. No other sorry, admit or native_decide is in the source closure.

## Modules (checkpoint after each compile)

| module | source lines | ported lines | decls kept/source | status |
|---|---|---|---|---|
| SchoenfeldPort.ChebyshevExplicit.Psi30 | 176 | 77 | 5/12 | compiles |
| SchoenfeldPort.ChebyshevExplicit.Psi30Upper | 230 | 220 | 10/11 | compiles |
| SchoenfeldPort.ChenExplicit.GammaBounds | 202 | 38 | 3/18 | compiles |
| SchoenfeldPort.ChirreHagen2025.Lemma26HSW | 392 | 65 | 6/33 | compiles |
| SchoenfeldPort.ChirreHagen2025.Lemma26Proof | 375 | 79 | 8/31 | compiles |
| SchoenfeldPort.ChirreHagen2025.SmoothTheorem2 | 372 | 32 | 1/15 | compiles |
| SchoenfeldPort.Dudek2014.Display | 158 | 31 | 1/11 | compiles |
| SchoenfeldPort.Dudek2014.Lemma5 | 122 | 54 | 2/7 | compiles |
| SchoenfeldPort.Dudek2014.Section22 | 418 | 63 | 2/16 | compiles |
| SchoenfeldPort.Dudek2014.SigmaHSW | 384 | 295 | 19/21 | compiles |
| SchoenfeldPort.Dudek2014.SigmaTrudgian | 548 | 389 | 42/48 | compiles |
| SchoenfeldPort.Final | new | 58 | -/- | compiles |
| SchoenfeldPort.Helfgott2013.GammaFine | 156 | 113 | 10/14 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.DudekLemma4 | 213 | 167 | 11/15 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.DudekTrudgian | 133 | 110 | 8/10 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Edges | 262 | 247 | 17/18 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Final | 207 | 187 | 6/7 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.FirstDiffHSW | 301 | 296 | 16/16 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.LeftZeta | 403 | 398 | 12/12 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Log2Pi | 46 | 26 | 1/2 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Merom | 163 | 158 | 12/12 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Nontrivial | 64 | 59 | 2/2 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.PsiSchoenfeld | 94 | 89 | 4/4 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.PsiSchoenfeldLarge | 367 | 362 | 5/5 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.PsiUnsmooth | 160 | 69 | 1/6 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.Residues | 246 | 241 | 15/15 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge | 110 | 98 | 4/5 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.TrivialLimit | 347 | 342 | 12/12 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.TrivialRect | 352 | 347 | 12/12 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.ZeroSum | 226 | 221 | 11/11 | compiles |
| SchoenfeldPort.PNTPort.ExplicitPsi1.ZetaTwo | 155 | 150 | 11/11 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.Auxiliary | 85 | 34 | 3/12 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.EulerMaclaurin | 86 | 77 | 6/7 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.MediumPNT | 3512 | 73 | 3/71 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.Rectangle | 280 | 83 | 13/43 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.ResidueCalcOnRectangles | 1149 | 747 | 51/84 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.Sobolev | 369 | 160 | 20/41 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.StrongPNT | 2039 | 900 | 33/66 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.ZetaBounds | 3106 | 639 | 36/155 | compiles |
| SchoenfeldPort.PNTPort.StrongPNT.ZetaConj | 39 | 25 | 3/5 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.Count | 300 | 295 | 23/23 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.Digamma | 222 | 36 | 2/7 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.Digamma2 | 378 | 373 | 12/12 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.GammaBounds | 201 | 60 | 3/10 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.GoodHeight | 327 | 322 | 6/6 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.LeftHalf | 150 | 145 | 3/3 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.LeftLine | 140 | 135 | 3/3 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.LocalPF | 178 | 173 | 7/7 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.Perron1 | 243 | 238 | 15/15 | compiles |
| SchoenfeldPort.PNTPort.ZetaZeros.Sym | 231 | 228 | 20/20 | compiles |

Totals: 50 modules, 9824 ported lines.

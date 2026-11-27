# Schoenfeld S1, progress (chunk 1, 11-27-2026)

Goal of S1: prove the three hypotheses `HSWN70 gZ`, `HSWHead14 gZ`, `Ordinates14 gZ` of the ported
`SchoenfeldPort.schoenfeld_psi_large` (folder `~/HaveMindHive/schoenfeld-port_v1.0_11-27-2026/`), so
that `|ψ(x) - x| ≤ √x log² x / (8π)` for `x ≥ 10^11` holds with no hypothesis. Environment: the
riemann-hypothesis-community repository (Lean v4.37.0-rc1, Mathlib 31ce06ea, Tau Ceti), read-only;
RH is `riemannHypothesis` (Alpöge with Claude). Local work only, never pushed.

Delivered files are sorry-free; `#print axioms` of every main result: `[propext, Classical.choice,
Quot.sound]` (scratch/axioms-A-B.txt and the S1E check). No `native_decide`.

## Files

| file | module | status |
|---|---|---|
| `S1A_v1.0_11-27-2026.lean` | `SchoenfeldS1.A` | compiles, olean in build/ |
| `S1B_v1.0_11-27-2026.lean` | `SchoenfeldS1.B` | compiles, olean in build/ |
| `S1D_v1.0_11-27-2026.lean` | `SchoenfeldS1.D` | compiles, olean in build/ |
| `S1E_v1.0_11-27-2026.lean` | `SchoenfeldS1.E` | compiles, olean in build/ |
| `tools/lean1_v1.0_11-27-2026.sh FILE` | check a file against build/ + the port's oleans + the RH repo | |
| `tools/build1_v1.0_11-27-2026.sh M` | compile `S1M_v1.0_11-27-2026.lean` to `build/SchoenfeldS1/M.olean` (copies it to `src/SchoenfeldS1/M.lean` for the module name) | |
| `tools/build_tauceti1_v1.0_11-27-2026.sh` | attempt to compile unbuilt Tau Ceti modules locally; does NOT work for module-system files (see Findings 5) | |
| `tools/mirror_v1.0_11-27-2026.sh` | rsync to OneDrive without build/, scratch/ | |

Check time: about 30 s per file (imports of `SchoenfeldPort.Final` load the whole port).

## Proven (exact statements)

### S1A, the counting bridge (target (E) wiring, done; no RH used)

```
def zerosBand (a b : ℝ) : Set ℂ := {ρ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < ρ.im ∧ ρ.im ≤ b}
noncomputable def zerosBandF (a b : ℝ) : Finset ℂ   -- its finite set (from the port's zeros_rect_finite)
noncomputable def Nband (a b : ℝ) : ℕ := ∑ ρ ∈ zerosBandF a b, analyticOrderNatAt ζ ρ
noncomputable def NT (T : ℝ) : ℕ := Nband 0 T       -- the classical N(T), with multiplicity

theorem card_filter_le_two_mul_Nband (s : Finset ZIdx) {a b : ℝ} (ha : 0 ≤ a) :
    (s.filter (fun i => a < |gZ i| ∧ |gZ i| ≤ b)).card ≤ 2 * Nband a b
theorem card_filter_abs_le_le (s : Finset ZIdx) (T : ℝ) :
    ((s.filter (fun i => |gZ i| ≤ T)).card : ℝ) ≤ 2 * NT T
lemma Nband_add {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) : Nband 0 t = Nband 0 T + Nband T t
lemma im_ne_zero_of_zero {ρ : ℂ} (hz : ζ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.im ≠ 0
theorem HSWHead14_of_NT (h : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T) : HSWHead14 gZ
theorem HSWN70_of_NT (hU : ∀ T : ℝ, 70 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T)
    (hL : ∀ T : ℝ, 70 ≤ T → Mt T - Rt T ≤ NT T) : HSWN70 gZ
theorem Ordinates14_of_zeroFree (h : ∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 14 ≤ |ρ.im|) : Ordinates14 gZ
theorem Ordinates14_of_NT (h : NT 14 = 0) : Ordinates14 gZ
```
The factor 2 is the reflection `ρ ↦ 1 - ρ` (functional equation; multiplicity by the port's
`SchoenfeldPort.PNTPort.ZetaZeros.ord_one_sub`), not conjugation, so RH is not needed. "No real zero in
(0,1)" is `TauCeti.riemannZeta_lt_zero`.

### S1B, explicit Stirling for the Riemann-Siegel theta (target (B), done)

```
noncomputable def zTheta (T : ℝ) : ℂ := ⟨1 / 4, T / 2⟩
noncomputable def rsTheta (T : ℝ) : ℝ := (TauCeti.logGamma (zTheta T)).im - T / 2 * Real.log π
noncomputable def rsThetaMain (T : ℝ) : ℝ := T / 2 * Real.log (T / (2 * π)) - T / 2 - π / 8
theorem abs_rsTheta_sub_main_le {T : ℝ} (hT : 0 < T) : |rsTheta T - rsThetaMain T| ≤ 11 / (16 * T)
theorem abs_rsTheta_sub_main_le_of_fourteen_le {T : ℝ} (hT : 14 ≤ T) : |rsTheta T - rsThetaMain T| ≤ 11 / 224
theorem rsTheta_zero : rsTheta 0 = 0
```
Pieces: `(T/2)(log ‖z‖ - log(T/2)) ∈ [0, 1/(16T)]`, `(1/4) arctan(1/(2T)) ∈ [0, 1/(8T)]`,
`|Im stirlingRemainder z| ≤ 1/(8 cos²(arg z/2) ‖z‖) ≤ 1/(2T)` (Tau Ceti's Nemes bound
`TauCeti.norm_stirlingRemainder_le`, with `0 ≤ arg z ≤ π/2`, `‖z‖ ≥ T/2`). The true size is
`1/(48T) + O(T⁻³)`; `11/(16T)` is what the one-term Nemes bound gives without more work. This
`rsTheta` is the continuous branch (`rsTheta 0 = 0`), the one that enters `N(T) = θ(T)/π + 1 + S(T)`.

### S1D, Backlund disc ingredients (target (D) groundwork, done; scratch/axioms-D.txt)

```
theorem norm_riemannZeta_le_on_disc {T : ℝ} (hT : 3 ≤ T) {s : ℂ}
    (hs : ‖s - (2 + T * I)‖ ≤ 7 / 4) : ‖ζ s‖ ≤ 4 * T + 24
theorem re_riemannZeta_two_add_ge (T : ℝ) : 2 - π ^ 2 / 6 ≤ (ζ (2 + T * I)).re
```
The first is the port's `norm_zeta_le` (`‖ζ s‖ ≤ 2 + ‖s‖/Re s`) on the disc (crude: the
convexity bound would give `O(T^{1/2} log T)` there). The second is the Jensen centre value
`|g(2 + iT)| = |Re ζ(2 + iT)| ≥ 2 - π²/6 = 0.355...` from the Dirichlet series. With these, Jensen on
the disc of radius `7/4` (zeros counted on radius `3/2`) gives the crude Backlund bound
`#{zeros of Re ζ(σ + iT), 1/2 ≤ σ ≤ 2} ≤ log((4T + 24)/0.355)/log(7/6)`, i.e. `C₁ᵉ ≈ 1/(2 log(7/6))
≈ 3.24` in `|S(T)|`; by Finding 6 that constant is absorbed at `x₀ ≈ 10^14` to `10^15`.

### S1E, the target restated (target (E) wiring, done)

```
theorem schoenfeld_psi_large_of_NT
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + Rt T)
    (hL : ∀ T : ℝ, 70 ≤ T → Mt T - Rt T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 11, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π)
theorem schoenfeld_theta_large_of_NT (same) : ∀ x ≥ 10 ^ 11, |θ x - x| ≤ √x * log x ^ 2 / (8 * π)
```
with `Mt T = T/(2π) log(T/(2πe)) + 7/8`, `Rt T = 0.1038 log T + 0.2573 log log T + 10.2425`.
S1 is now exactly these three real statements about `NT`.

## Status of (A) to (E)

* (A) Ordinates14: reduced to `NT 14 = 0` (S1A). Not proven. Sizing below.
* (B) Stirling for theta: done (S1B), constant `11/(16T)`.
* (C) `N(T) = θ(T)/π + 1 + S(T)`: not started in Lean. Design below.
* (D) explicit `|S(T)|`: the two disc ingredients are proven (S1D); Jensen step and the argument
  bookkeeping not started. Literature read (HSW source), findings below.
* (E) assembly: done modulo (A), (C), (D) (S1E).

## Findings that change the S1 estimate

1. **HSW's constant 9.3675 rests on a zero database.** From the TeX source of arXiv 2107.06506
   (Hasanalizade, Shen, Wong; fetched 11-27-2026, scratch/hsw/hsw.tex): Theorem 1.1 states, for
   `T ≥ T₀`,
   `|N(T) - (T/2π) log(T/(2πe)) + 1/8| ≤ C₁ log T + C₂ log log T + C₃`
   with `C₃` depending on `T₀`. Table 2 (computed with `T₀ = 30 610 046 000`, `J₁ = 64`, `J₂ = 39`):
   | c | r | η | C₁ | C₂ | C₃ | C₃' |
   |---|---|---|---|---|---|---|
   | 1.000011314 | 1.064340602 | 4.2826451e-6 | 0.103787 | 0.257297 | 9.367419 | 8.367419 |
   | 1.025253504 | 1.182375395 | 0.009944751381 | 0.109410 | 0.204142 | 4.030486 | 3.030486 |
   | 1.035766557 | 1.229059659 | 0.014325507360 | 0.111973 | 0.189768 | 3.746756 | 2.746756 |
   Corollary 1.2 (`T ≥ e`, constant 9.3675) is proved for `e ≤ T ≤ 30 610 046 000` from
   `|S(T)| ≤ 2.5167` on that range, which comes from Platt's zero database (LMFDB), eq. (bd-S).
   A formal proof cannot use that. The analytic theorem with small `T₀` is what S1 can aim at.
   The `T₀`-dependence of `C̃₃` (eq. def-C3) is only the terms `(640δ-112)/(1536(3T₀-1))`,
   `1/(25T₀)` and `κ₃(T₀) = O(1/T₀)`, so `T₀ = 70` costs little (order 0.1 in `C₃`, to be
   computed exactly next chunk); the cost is not in `T₀`.
2. **Where the slack is.** Writing HSW's theorem form with the port's `Mt`, `Rt`
   (`Mt + Rt = main + 7/8 + R + 10.2425`, `Mt - Rt = main - R - 9.3675`, `R = 0.1038 log T + 0.2573 log log T`):
   the upper clause (`HSWHead14`, first clause of `HSWN70`) needs `C₃ ≤ 11.2425` (slack 1.875 over
   HSW's 9.367419); the lower clause (second clause of `HSWN70`, only for `T ≥ 70`) needs
   `C₃ ≤ 9.2425`, which HSW's own Table 2 value 9.367419 does **not** meet. (Side remark: for
   `T ≥ T₀` the printed Corollary 1.2 lower bound seems to need `C₃ + 1/8 ≤ 9.3675`, which the
   table does not give; this looks like a 1/8 slip in the paper's lower side. Verify before relying
   on it.) So even a full formalization of HSW would leave the lower clause 0.125 short; the lower
   clause must be absorbed on the S2 side (it enters only `SigmaHSW.lean`'s tail estimates, where
   `Rt` is split as `Mt T - Rt T`), or `Rt`'s constant raised there.
3. **HSW's `C₁ = 0.1038` needs subconvexity.** Their inputs: Patel `|ζ(1+it)| ≤ log t` (`t ≥ 3`),
   Hiary (as corrected by Patel) `|ζ(1/2+it)| ≤ 0.77 t^{1/6} log t` (`t ≥ 3`), and a weighted Jensen
   (`F_{c,r}`) with 64 + 39 numerically integrated pieces. Formalizing Hiary's Weyl-type bound is
   far outside S1's budget. A convexity-only Backlund/Rosser argument gives a larger `C₁`
   (classically about 0.137 log T + 0.443 log log T + c; fetch Backlund 1918 / Rosser 1941 /
   Trudgian 2014 before quoting). **Consequence: S1 as stated (reaching `Rt`) is very likely out of
   reach; the realistic S1 output is a weaker `Rt'` with `C₁ ≈ 0.14` to `0.2`, and an S2-side audit
   of `SigmaHSW.lean`, `Lemma26HSW.lean`, `FirstDiffHSW.lean` (where `Rt` enters) to see whether
   `Rt'` is absorbed, possibly raising `10^11`.** This audit should be the first job of chunk 2,
   because it decides what constants S1 must reach.
4. **(A) sizing.** mpmath survey (scratch, not a proof): `min |ζ(1/2+it)|` on `[0,14]` is 0.10563 at
   `t = 14` (the first zero is at 14.1347...), `max |ζ'(1/2+it)|` on `[0,14]` is 3.923 (at `t = 0`),
   `max |Z'(t)|` is 1.035, `θ(14)/π + 1 = 0.4325`. A rigorous grid proof of `ζ(1/2+it) ≠ 0` on
   `[0,14]` via a Lipschitz bound 4 needs about 560 points with `|ζ|` enclosed to within 0.03
   each, i.e. about 15 000 certified enclosures of `cos/sin(t log n)`, `n^{-1/2}` for `n ≤ 30`
   (Euler-Maclaurin with 2 Bernoulli corrections, remainder below 1e-4 for `N = 30`). No
   interval-arithmetic tactic exists in this Mathlib/Tau Ceti; the proofs must be generated
   (Python emits Lean, rational enclosures, `Real.cos_bound`/`Real.sin_bound`/`Real.exp_bound`
   style lemmas, `norm_num`). Estimate 15 to 30 agent-hours plus kernel time; a separate
   sub-project, independent of (C)/(D). Under RH (available), only the line `Re = 1/2` matters.
5. **Tau Ceti's `S(T)` is not built.** `TauCeti.LFunctions.riemannZetaS` (RiemannVonMangoldt/Argument.lean)
   and its continuous-argument characterizations `riemannZetaS_eq_sub_div_pi`,
   `exists_riemannZetaS_eq_div_pi` are exactly what (C) wants, but the RH repo's build does not
   include that module; the unbuilt closure is 5 modules, 1853 lines (Argument, Contour/Argument/Lift,
   Topology/Circle/Degree, Contour/Argument/Variation, Contour/Winding/SegmentSum). They are
   module-system files (`module`, `public import`) and `lean --root ... -o ...` from outside lake does
   not resolve their imports (scratch/tauceti-build.log). Options: (i) ask the owner to run
   `lake build TauCeti.NumberTheory.LFunctions.Zeros.RiemannVonMangoldt.Argument` inside the RH repo
   (writes only `.lake` artifacts); (ii) define `S(T)` ourselves through the port's rectangle
   machinery (`ResidueCalcOnRectangles`, `Merom`, `TrivialRect`) and the argument principle; (ii)
   is more work but self-contained. Also unbuilt: `Analysis/Meromorphic/Counting/Certificate.lean`
   (209 lines) and `LFunctions/Zeros/Counting/Basic.lean` (+Rectangle, 388 lines).

6. **S2-absorption audit (first pass, done in chunk 1): the port does NOT need HSW's constants.**
   `Rt` enters the ported proof at exactly four places, all of which only use linearized majorants:
   * `SigmaHSW.Rt_le : Rt t ≤ 0.251 log t + 10.25` (`t ≥ 70`; the `log log` term is absorbed via
     `log_le_half`) and `Rt_nonneg`, feeding `head_count` (`N ≤ T log T/π - (0.89T - 22.25 - 0.502 log T)`),
     `AT = 20.5 + 2 Rt T`, `H2_bound`, `tail_inv_sq`, `slack` (needs
     `1.1 (1.004 log T + 41.26 - 0.25 T) ≤ 0.89 T - 22.25 - 0.502 log T` at `T ≥ 70`).
   * `FirstDiffHSW.count_major : 2 (Mt t + Rt t) ≤ mF t = t(log t - log 2π - 1)/π + 22.25 + 0.502 log t`
     (`t ≥ 14`), feeding `head_inv : Σ_{|γ| ≤ T} 1/|γ| ≤ (log T - log 2π)²/(2π) + 1.57`, i.e. the
     head factor `S1 T` with constant `K = 1.57`; the tail factor
     `S2 T = log T/(πT) + (1.004 log T + 41.26 - 0.25T)/T²`.
   * In `PsiSchoenfeldLarge`, `T = 2π√x / log x` (about 78 500 at `x = 10^11`), so the `70 ≤ T`
     threshold of the tail estimates can be raised to anything below about `7·10^4` for free, and
     the final inequality `core` consumes `K`, `1.004`, `41.26` as numerals.
   Measured margins (Python on the exact `core` expression, worst case `E = 4`, scratch):
   | `x₀` | max `K` in `core` |
   |---|---|
   | 10^11 | 2.546 (margin 0.976 √x) |
   | 10^12 | 3.318 |
   | 10^13 | 4.123 |
   | 10^15 | 5.822 |
   | 10^17 | 7.629 |
   The tail numerals are insensitive: `(1.004 M + 41.26) L/(2π²) ≤ 0.0035 √x` holds with a factor
   16 to spare at `10^11`, so `C₁', C₃'` up to about `15` and `300` there. For the head, with the
   majorant `N(t) ≤ main(t) + 7/8 + C₁ᵉ log t + C₃'` (`C₁ᵉ` = `C₁'` plus the absorbed `log log`
   coefficient, currently `0.251`), `K` moves by `2 ΔC₃'/14 = 0.143 ΔC₃'` and by
   `2 ΔC₁ᵉ (log 14 + 1)/14 = 0.52 ΔC₁ᵉ` (the port's `(22.25, 0.502)` contribute `1.72`, other terms
   `-0.15`). So at `x₀ = 10^11` the port absorbs any explicit bound with `0.143 ΔC₃' + 0.52 ΔC₁ᵉ ≤ 0.97`:
   e.g. `C₃'` up to `17` with `C₁ᵉ` fixed, or `C₁ᵉ` up to `2.1` with `C₃'` fixed; a classical
   Backlund/Rosser-type bound (`C₁ ≈ 0.14`, `C₂ ≈ 0.44`, `C₃` a few units) fits at `10^11`; a crude
   Backlund bound with `C₁ᵉ ≈ 3.3` needs `x₀ ≈ 10^14` to `10^15`. The lower clause problem of
   Finding 2 disappears once `Rt` is replaced by whatever `Rt'` S1 proves. The S2-side cost is a
   re-proof of `Rt_le`, `count_major`, `head_inv`, `head_count`, `AT_le`, `slack`, `H2_bound`
   and the numerals in `S1`, `S2`, `core`, `large_facts` (a few hours of `nlinarith` work).
   These margins are rough (one Python evaluation); redo them in Lean when `Rt'` is known.

## NEXT-CHUNK plan (chunk 2)

1. **Fix the S1 target from Finding 6 (1 h).** Decide `Rt'` and `x₀`: aim at a Backlund-type
   `C₁ᵉ ≤ 0.5`, `C₃' ≤ 12` at `x₀ = 10^11`, fall back to `x₀ = 10^14` if only the crude disc bound
   is reached. Write the modified `SigmaHSW`/`FirstDiffHSW`/`PsiSchoenfeldLarge` numerals as a
   checklist (copies in this folder only; the port is not modified).
2. **Compute HSW's `C₃` at `T₀ = 70` and `T₀ = 14` (1 h, Python from eq. def-C3 and κ₃)** to
   quantify Finding 1 precisely. Fetch Backlund 1918, Rosser 1941 (Trudgian 2014 is reported
   flawed by HSW: the `|ζ(1+it)| ≤ (3/4) log t` input) for the convexity-only constants.
3. **(C) in Lean (15 to 25 h).** Definition: with `rsTheta` of S1B, prove for `T ≥ 14` not an
   ordinate: `(NT T : ℝ) = rsTheta T / π + 1 + S T`, `S` defined as the argument change along
   `2 → 2 + iT → 1/2 + iT` (either Tau Ceti's `riemannZetaS` once built, or our own via the port's
   rectangle residue theorem on `[-1/2... ]`, using `Zall_eq`, `ord_one_sub`, the functional
   equation `riemannZeta_one_sub`, and `TauCeti.logGamma`). The `+1` is the pole at `s = 1`; the
   zeros at `Re = 1/2` are handled by the symmetry `ρ ↦ 1 - ρ` (already in S1A). First
   milestone: the identity for the symmetric rectangle `[-1, 2] × [-T, T]` with the completed
   `ξ`, then the half-count.
4. **(D) Backlund-style `|S(T)|` (25 to 40 h).** Jensen on the disc centre `2 + iT`, radius
   `r ∈ (3/2, 2)`, for `g(s) = (ζ(s + iT) + ζ(s - iT))/2`; `|g(2)| ≥ 2 - ζ(2) = 0.355...`;
   `|ζ|` on the disc from the port's `norm_zeta_le` (`‖ζ s‖ ≤ 2 + ‖s‖/Re s`, crude, gives
   `C₁ ≈ 3`) first, then the convexity bound (Tau Ceti `RiemannZeta/Bounds.lean`,
   `EulerMaclaurin.lean`; ExplicitRH's `norm_LFunctionTrivChar₁_one_le_pow_mul` on the disc of
   radius 31/16) to approach `0.137`. Deliver the crude constant sorry-free first.
5. **(A) certified evaluation (15 to 30 h, independent; can run in parallel as its own agent).**
   Generator script + one Lean lemma per grid point; no `native_decide`.

Revised S1 total: with Finding 6 the port tolerates a convexity-only (even a crude disc-bound)
`Rt'` at `x₀` between `10^11` and `10^15`, so the original 60 to 150 h estimate stands for
(C) + (D) + (A) + the S2 numeral re-proof, with the crude-constant version at the low end. Reaching
HSW's own `0.1038 log T` is not needed and not attempted.

## Rules kept
The banned prime-method words, the legacy three-letter residue-theorem abbreviation and em-dashes
do not occur (grep check each milestone); Apache-2.0 attribution in each file header (goldbach-lean: Steve
Hubbard; Tau Ceti contributors; RH: Alpöge with Claude); constants quoted from the fetched HSW
source only.

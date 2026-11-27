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
| `S1E_v1.0_11-27-2026.lean` | `SchoenfeldS1.E` | compiles, olean in build/ (HSW `Rt`, `x ≥ 10^11`; superseded by G) |
| `S1F_v1.0_11-27-2026.lean` | `SchoenfeldS1.F` | chunk 2: counts with `RtB`, compiles, olean in build/ |
| `S1G_v1.0_11-27-2026.lean` | `SchoenfeldS1.G` | chunk 2: ψ, θ bounds for `x ≥ 10^15` from `N(T)` with `RtB`, compiles, olean |
| `S1D2_v1.0_11-27-2026.lean` | `SchoenfeldS1.D2` | chunk 2: Backlund disc function and Jensen's count, compiles, olean |
| `S1C_WIP_v1.0_11-27-2026.lean` | (WIP, `sorry`) | chunk 2: exact target statements for (C), (D), (U'), (L'), the final theorem; type-checks |
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

## Chunk 2 plan as written at the end of chunk 1 (superseded by the chunk 2 section and the chunk 3 plan below; kept for the record)

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

## Chunk 2 (11-27-2026, 13:50 to 14:25): goal 1 done, (D) half done, (C) stated

Owner's go: "keep going". Local only, nothing pushed; the port and the RH repo sources untouched
(one `lake build` of a Tau Ceti module in the RH repo, writing only `.lake` artifacts, see below).

### Decision: `RtB T = 4.5 log T + 17.1`, `x₀ = 10^15`, tail threshold `1000`

Why these numbers (scratch, Python `consts.py`, mpmath 30 digits):
* Backlund's disc with the crude bound of the port (`‖ζ s‖ ≤ 2 + ‖s‖/Re s`) on the disc of radius
  `R = 15/8` about `2 + iT` (`Re s ≥ 1/8`): `‖ζ‖ ≤ 8T + 48`; Jensen with `r = 3/2` (covers
  `1/2 ≤ σ ≤ 2`) and `|g(2)| ≥ 2 - π²/6 = 0.3550...` gives at most
  `log((8T + 48)/0.3550)/log(5/4)` zeros, `1/log(5/4) = 4.48142...`, and for `T ≥ 14`
  `log(8 + 48/14) - log(0.3550) = 3.4853...`, so count `≤ 4.4815 log T + 15.62`; the argument
  bookkeeping adds `3/2`, Stirling (S1B) adds `11/(224π) = 0.0156`; total `≤ 4.5 log T + 17.0957`
  (checked: `max_T≥14 [backlund(T) - (4.5 log T + 17.08)] = -0.0715`). Radius `7/4` (S1D's lemma)
  would give `6.4872 log T + 19.54` and need `x₀ = 10^16`.
* The port's `core` inequality with `RtB` (numerals `K = 4.8`, `2A₀ = 18`, `C₂ = 72.9`): margin
  `-1.25 √x` at `10^13`, `+0.14 √x` at `10^14`, `+1.00 √x` at `10^15`, `+1.89 √x` at `10^16`.
  `10^15` chosen for a comfortable `nlinarith`; `10^14` is possible with careful re-tuning
  (margin 0.14) and is noted as a later tightening.
* `slackB` (`1.1 (18 log T + 72.9 - 0.25 T) ≤ 0.89 T - 36 - 9 log T`) fails near `T = 70` and holds
  from about `T = 250`; the threshold was set to `1000` (needs only `log T ≤ T/100`). In S2,
  `T = 2π√x/log x ≥ 2π · 2530 > 15 000` already at `x ≥ 10^11`, so this is free.

Numeral checklist (port constant → S1F/S1G constant): `Rt_le (0.251, 10.25)` → none (`RtB` is
linear in `log`); `head_count (22.25, 0.502)` → `(36, 9)`; `AT = 20.5 + 2Rt` → `ATB = 34.2 + 2RtB`;
`AT_le (0.502, 41)` → `(9, 68.4)`; `H2_bound (1.004, 41.26)` → `(18, 72.9)`; `slack` at `70` →
`slackB` at `1000` via `log_le_hundredth`; `count_major mF (22.25, 0.502)` → `mFB (36, 9)`;
`head_inv 1.57` → `head_invB 4.8` (`(36 + 9 (log 14 + 1))/14 - 1/(2π) ≤ 4.95 - 0.158`);
`S1, S2` → `SB1, SB2`; `large_facts (316227, 25.3, L² ≤ s/100, 3.2)` →
`large_factsB (31622776, 34.5, L² ≤ s/10000, 3.5)`; `core` → `coreB` (intermediate slack
`0.0002 s → 0.0004 s`, `1.2122 → 1.2124`, product hints `(l - 3.5)(L/7 - l) ≥ 0`,
`(l - 3.5)(L - 34.5) ≥ 0`).

### Proven (exact statements), all sorry-free, axioms `[propext, Classical.choice, Quot.sound]`
(scratch/axioms-G.txt, scratch/axioms-D2.txt)

S1F (`SchoenfeldS1.F`):
```
noncomputable def RtB (T : ℝ) : ℝ := 4.5 * log T + 17.1
def NB1000 (γ : ι → ℝ) : Prop := (∀ T ≥ 1000, ∀ s, #{i ∈ s | |γ i| ≤ T} ≤ 2 (Mt T + RtB T)) ∧
  (∀ T t, 1000 ≤ T → T ≤ t → ∀ s, #{i ∈ s | T < |γ i| ≤ t} ≤ 2 ((Mt t + RtB t) - (Mt T - RtB T)))
def NBHead14 (γ : ι → ℝ) : Prop := ∀ T ≥ 14, ∀ s, #{i ∈ s | |γ i| ≤ T} ≤ 2 (Mt T + RtB T)
lemma head_countB (hN : NB1000 γ) (hT : 1000 ≤ T) (s) : #{|γ| ≤ T} ≤ T log T/π - (0.89 T - 36 - 9 log T)
lemma tail_inv_sqB (hN : NB1000 γ) (hT : 1000 ≤ T) (s) :
    Σ_{i ∈ s, ¬|γ i| ≤ T} 1/γ i² ≤ log T/(πT) + (18 log T + 72.9 - 0.25 T)/T²
lemma slackB (hT : 1000 ≤ T) : 0 ≤ 0.89 T - 36 - 9 log T ∧ 1.1 (18 log T + 72.9 - 0.25 T) ≤ 0.89 T - 36 - 9 log T
lemma count_majorB (ht : 14 ≤ t) : 2 (Mt t + RtB t) ≤ mFB t   -- mFB t = t(log t - log 2π - 1)/π + 36 + 9 log t
lemma head_invB (hN : NBHead14 γ) (h14 : ∀ i, 14 ≤ |γ i|) (hT : 14 ≤ T) (s) :
    Σ_{i ∈ s, |γ i| ≤ T} 1/|γ i| ≤ (log T - log 2π)²/(2π) + 4.8
theorem zdiff_leB (hN : NB1000 γ) (hH : NBHead14 γ) (h14) (hx : 0 < x) (hh : 0 ≤ h) (hT : 1000 ≤ T) :
    ‖Σ' fz (x+h) - Σ' fz x‖ ≤ h (x+h)^{1/2} SB1 T + 2 (x+h)^{3/2} SB2 T
```
S1G (`SchoenfeldS1.G`):
```
theorem psi_upper_genB / psi_lower_genB  (as the port's, with SB1, SB2, 1000 ≤ T)
lemma large_factsB (hx : 10^15 ≤ x) : 31622776 ≤ √x ∧ 34.5 ≤ log x ∧ log x² ≤ √x/10000 ∧
    3.5 ≤ log (log x) ∧ log (log x) ≤ log x/7 ∧ log x = 2 log √x
lemma coreB  (the port's core with 4.8, 18, 72.9 and the 10^15 facts)
theorem psi_schoenfeld_large_slackB (hRH) (hN : NB1000 gZ) (hH : NBHead14 gZ) (h14 : Ordinates14 gZ)
    (hx : 10^15 ≤ x) : |psiF x - x| ≤ √x log² x/(8π) - 1.2 √x
theorem psi_schoenfeld_largeB (hN) (hH) (h14) : ∀ x ≥ 10^15, |ψ x - x| ≤ √x log² x/(8π)
theorem theta_schoenfeld_largeB (hN) (hH) (h14) : ∀ x ≥ 10^15, |θ x - x| ≤ √x log² x/(8π)
theorem NBHead14_of_NT (h : ∀ T ≥ 14, (NT T : ℝ) ≤ Mt T + RtB T) : NBHead14 gZ
theorem NB1000_of_NT (hU : ∀ T ≥ 1000, NT T ≤ Mt T + RtB T) (hL : ∀ T ≥ 1000, Mt T - RtB T ≤ NT T) : NB1000 gZ
theorem schoenfeld_psi_large_of_NTB
    (hU : ∀ T : ℝ, 14 ≤ T → (NT T : ℝ) ≤ Mt T + RtB T)
    (hL : ∀ T : ℝ, 1000 ≤ T → Mt T - RtB T ≤ NT T)
    (h14 : NT 14 = 0) :
    ∀ x ≥ (10 : ℝ) ^ 15, |ψ x - x| ≤ √x * log x ^ 2 / (8 * π)
theorem schoenfeld_theta_large_of_NTB (same hypotheses) : ∀ x ≥ 10^15, |θ x - x| ≤ √x log² x/(8π)
```
S1D2 (`SchoenfeldS1.D2`), target (D) groundwork:
```
theorem norm_riemannZeta_le_on_disc' (hT : 3 ≤ T) (hs : ‖s - (2 + T I)‖ ≤ 15/8) : ‖ζ s‖ ≤ 8 T + 48
noncomputable def gB (T : ℝ) (z : ℂ) : ℂ := (ζ (z + T I) + ζ (z - T I)) / 2
lemma gB_eq_re_of_real (T σ : ℝ) : gB T σ = ((ζ (σ + T I)).re : ℂ)        -- riemannZeta_conj
theorem analyticOnNhd_gB (hT : 3 ≤ T) : AnalyticOnNhd ℂ (gB T) (closedBall 2 (15/8))
theorem norm_gB_le (hT : 3 ≤ T) (hz : z ∈ closedBall 2 (15/8)) : ‖gB T z‖ ≤ 8 T + 48
theorem norm_gB_two_ge (T) : 2 - π²/6 ≤ ‖gB T 2‖ ;  theorem gB_two_ne_zero (T) : gB T 2 ≠ 0
theorem sum_divisor_gB_le (hT : 3 ≤ T) :
    ((Σᶠ u, MeromorphicOn.divisor (gB T) (closedBall 2 (3/2)) u : ℤ) : ℝ)
      ≤ log ((8 T + 48)/(2 - π²/6)) / log (5/4)                        -- Mathlib AnalyticOnNhd.sum_divisor_le
theorem card_le_sum_divisor (hr : 0 ≤ r) (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hc : f c ≠ 0)
    (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ closedBall c r ∧ f z = 0) : (s.card : ℤ) ≤ Σᶠ u, divisor f (closedBall c r) u
theorem card_zeros_gB_le (hT : 3 ≤ T) (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ closedBall 2 (3/2) ∧ gB T z = 0) :
    (s.card : ℝ) ≤ log ((8 T + 48)/(2 - π²/6)) / log (5/4)
```
Mathlib already has Jensen's inequality for zero counts (`AnalyticOnNhd.sum_divisor_le`,
Mathlib/Analysis/Complex/JensenFormula.lean), so the disc step of (D) cost 200 lines, not the
25 h estimated. The identity theorem (`eqOn_zero_of_preconnected_of_eventuallyEq_zero`) excludes
infinite order since `gB T 2 ≠ 0`.

### Tau Ceti's `S(T)` is now built (Finding 5 resolved)

`lake build --fail-fast +TauCeti.NumberTheory.LFunctions.Zeros.RiemannVonMangoldt.Argument:olean`
in the RH repo finished in under a minute (its 5 unbuilt dependencies were cached except the
elaboration); only `.lake/packages/TauCeti/.lake/build` was written. `riemannZetaS T`,
`riemannZetaS_eq_sub_div_pi`, `exists_riemannZetaS_eq_div_pi` import fine from S1 files
(`S1C_WIP` imports the module). `lake build` does not accept `-j`; it used the machine's cores for
the minute it ran.

### Literature constants for `|S(T)| ≤ a log T + b log log T + c` (fetched 11-27-2026, agent report)

Read on https://arxiv.org/html/1208.5846v2 (Trudgian, arXiv 1208.5846 v2, Table 1 and Theorem 1;
journal version J. Number Theory 134 (2014) 280-292 not read):
| source | a | b | c | T ≥ |
|---|---|---|---|---|
| Backlund 1914 (as tabulated by Trudgian) | 0.275 | 0.979 | 7.446 | 200 |
| Backlund 1918 (as tabulated by Trudgian) | 0.137 | 0.443 | 4.35 | 200 |
| Rosser 1941 (as tabulated by Trudgian) | 0.137 | 0.443 | 1.588 | 1467 |
| Trudgian 2012 (arXiv v2, Theorem 1) | 0.111 | 0.275 | 2.450 | e |
Hasanalizade-Shen-Wong (abstract, https://arxiv.org/abs/2107.06506): `0.1038, 0.2573, 9.3675` in
`N(T)` form; their introduction could not be fetched (HTML 404, PDF binary). Chunk 1 noted (from
the HSW TeX source) that HSW report Trudgian's input `|ζ(1+it)| ≤ (3/4) log t` as flawed.
Our `RtB` (`4.5, 0, 17.1`) is the crude-disc version; Backlund's own `0.137` needs the convexity
bound on the disc, not attempted.

### Status of (A) to (E) after chunk 2

* (A) `NT 14 = 0`: another agent (not touched here).
* (B) done (S1B).
* (C) `N(T) = θ(T)/π + 1 + S(T)`: stated exactly (`S1C_WIP.NT_eq_rsTheta_add`), proof not started.
* (D) `|S(T)|`: disc and Jensen count done (S1D2); the argument bookkeeping
  (`S1C_WIP.abs_riemannZetaS_le_backlund`: vertical segment `|θ| < π/2`, horizontal segment
  `≤ (q + 1) π` with `q ≤ card_zeros_gB_le`) not started; numeric form
  `abs_riemannZetaS_le : |S(T)| ≤ 4.5 log T + 17.08` stated.
* (E) done for `RtB`, `x₀ = 10^15` (S1G). `S1C_WIP.schoenfeld_psi_large_of_Z` type-checks: once
  `NT_le_Mt_add_RtB` and `Mt_sub_RtB_le_NT` are proven, `NT 14 = 0 → ∀ x ≥ 10^15, |ψ x - x| ≤ ...`
  is a one-liner from `schoenfeld_psi_large_of_NTB`.

## NEXT-CHUNK plan (chunk 3)

1. **(D) argument bookkeeping (8 to 15 h).** In `S1C_WIP` (move to a delivered `S1D3` when
   sorry-free): from `exists_riemannZetaS_eq_div_pi` take `θ` continuous on `[0, 2]`, `θ 0 = 0`,
   `ζ(path t) = ‖ζ(path t)‖ e^{iθ t}`.
   (a) Vertical segment `t ∈ [0, 1]`: `Re ζ(2 + itT) ≥ 2 - π²/6 > 0` (`re_riemannZeta_two_add_ge`),
   so `cos (θ t) > 0`; with `θ 0 = 0` and continuity, `θ t ∈ (-π/2, π/2)` (connectedness of
   `θ '' [0,1]`, `Real.cos_pos_of_mem_Ioo` and its converse).
   (b) Horizontal segment `t ∈ [1, 2]`, `σ = 2 - 3(t-1)/2 ∈ [1/2, 2]`: the set
   `Z = {t ∈ [1,2] : Re ζ(σ(t) + iT) = 0}` is finite with `|Z| ≤ card_zeros_gB_le` (map
   `t ↦ σ(t)` into zeros of `gB T` in `closedBall 2 (3/2)` by `gB_eq_re_of_real`; injective).
   Between consecutive points of `Z ∪ {1, 2}`, `cos (θ t) ≠ 0`, so `θ` stays in one interval
   `((k - 1/2)π, (k + 1/2)π)` and `|θ b - θ a| < π`; across a point of `Z` continuity gives the
   same bound for the closed subintervals. Induction over the sorted finset: `|θ 2 - θ 1| ≤ (|Z| + 1) π`.
   (c) `|S(T)| = |θ 2|/π ≤ |Z| + 1 + 1/2`. Then `abs_riemannZetaS_le` by the numerics above
   (`log((8T+48)/m₀) ≤ log T + 3.49`, `1/log(5/4) ≤ 4.4815`, Python-checked).
2. **(C) the identity (15 to 25 h).** Options, in order of preference: (i) look for the
   argument principle on rectangles in Tau Ceti (`Analysis/Meromorphic/Counting/Rectangle`,
   `LFunctions/Zeros/Counting/Basic` has `zeroCountingFunction` for completed L-functions; check
   whether a `zeroCount = winding/argument` theorem exists and is built); (ii) the port's
   `ResidueCalcOnRectangles` on `[-1, 2] × [0, T]` with `ξ` or with `ζ` plus the functional
   equation; the top edge gives `rsTheta` through `TauCeti.logGamma`. Write first the lemma
   `NT T = (number of zeros of ζ in the rectangle with 0 < Im ≤ T)` from `zerosBandF`.
3. **(U'), (L') from (C) + (D) (3 to 5 h):** `exists_notOrdinate_between` (finiteness of
   `zeros_rect_finite`), right-continuity of `NT` (`NT T = NT T'` for `T' ∈ (T, T + ε)`), monotonicity,
   continuity of `Mt ± RtB`; assemble `schoenfeld_psi_large_of_Z`.
4. Optional tightening: `x₀ = 10^14` (margin 0.14 √x) by re-tuning `coreB`; radius and
   centre choices in `S1D2` (e.g. `R = 2 - ε`) lower `a` toward `3.5`; the convexity bound would
   reach Backlund's `0.137`.
5. (A) stays with the other agent; the final theorem needs `NT 14 = 0` in the form of S1A's `NT`.

## Chunk 3 (11-27-2026, 14:20 to 15:30): (D) done, (U')/(L')/final assembled, (C) half done

Owner's go: "keep going". Local only, nothing pushed; the port and the RH repo sources untouched.
One `lake build` in the RH repo (`+TauCeti.Analysis.Contour.Argument.Rectangle.Variation:olean`,
`...Rectangle.Divisor`, `...Meromorphic.Counting.Rectangle`, `...LFunctions.Zeros.Counting.Basic`; 3 s,
all cached) wrote only `.lake` artifacts (scratch/c3/tauceti-build-rect.log). Checks take 2 to 6 s
per file now (oleans cached). The (A) sub-project is DONE by the other agent: `NT_fourteen_eq_zero`
(PROGRESS-s1z).

### Delivered (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`, no `native_decide`)

S1D3 (`SchoenfeldS1.D3`, scratch/axioms-D3.txt), target (D) complete:
```
def NotOrdinate (T : ℝ) : Prop := ∀ σ ∈ Ico (1/2) 1, ζ (σ + T I) ≠ 0
theorem abs_lt_pi_div_two_of_cos_pos (hθ : ContinuousOn θ (Icc a b)) (h0 : θ a = 0)
    (hcos : ∀ t ∈ Icc a b, 0 < cos (θ t)) : ∀ t ∈ Icc a b, |θ t| < π/2
theorem abs_sub_le_pi_of_cos_ne_zero (hab : a ≤ b) (hθ : ContinuousOn θ (Icc a b))
    (hcos : ∀ t ∈ Ioo a b, cos (θ t) ≠ 0) : |θ b - θ a| ≤ π
theorem abs_sub_le_of_finite_cos_zero (Z : Finset ℝ) : ∀ {b}, a ≤ b → ContinuousOn θ (Icc a b) →
    (∀ z ∈ Z, z ∈ Ioo a b) → (∀ t ∈ Ioo a b, t ∉ Z → cos (θ t) ≠ 0) → |θ b - θ a| ≤ (Z.card + 1) π
theorem abs_riemannZetaS_le_backlund (hT : 14 ≤ T) (hord : NotOrdinate T) :
    |riemannZetaS T| ≤ log ((8T + 48)/(2 - π²/6)) / log (5/4) + 3/2
theorem abs_riemannZetaS_le (hT : 14 ≤ T) (hord : NotOrdinate T) : |riemannZetaS T| ≤ 4.5 log T + 17.08
```
Numerics used (all proven in the file): `log(5/4) ≥ 0.22313` (`Real.abs_log_sub_add_sum_range_le`,
8 terms), `log(80/7) ≤ 2.44` (`exp_one_gt_d9`, 5 Taylor terms of `exp 0.44`),
`log(2 - π²/6) ≥ -1.04` (`pi_lt_d6`, `add_one_le_exp`), `log T ≥ 2` for `T ≥ 14`. The cosine
argument: `Re ζ(path t) = ‖ζ(path t)‖ cos θ t`; on `[0,1]` the real part is `≥ 2 - π²/6`; on `[1,2]`
the zero set of `cos θ` is `{t : gB T (σ t) = 0}`, finite with at most `q` points by
`card_zeros_gB_le` (`Set.Infinite.exists_subset_card_eq` for finiteness).

S1X (`SchoenfeldS1.X`, scratch/axioms-X-R.txt), the entire function for (C):
```
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1   -- = s(s-1)Λ(s) off 0,1
differentiable_xi, analyticOnNhd_xi, analyticAt_xi, continuous_xi, xi_zero : xi 0 = 1, xi_one : xi 1 = 1
xi_one_sub (s) : xi (1 - s) = xi s
xi_eq_mul (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) : xi s = s (s - 1) (Gammaℝ s ζ s)
xi_conj (s) : xi (conj s) = conj (xi s)                       -- Mathlib completedRiemannZeta_conj
xi_ne_zero_of_one_le_re, xi_ne_zero_of_re_nonpos, re_pos_lt_one_of_xi_eq_zero
xi_eq_zero_iff (h0 : 0 < s.re) (h1 : s.re < 1) : xi s = 0 ↔ ζ s = 0
analyticAt_Gammaℝ_of_re_pos (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s
analyticOrderNatAt_xi (h0) (h1) : analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ
Gammaℝ_ofReal_pos (hσ : 0 < σ) : Gammaℝ σ = ↑(π^(-σ/2) Real.Gamma (σ/2)) ∧ 0 < π^(-σ/2) Real.Gamma (σ/2)
xi_ofReal_pos (σ : ℝ) : xi σ = ((xi σ).re : ℂ) ∧ 0 < (xi σ).re ;  xi_ofReal_ne_zero
xi_ne_zero_of_notOrdinate (hord : ∀ σ ∈ Ico (1/2) 1, ζ (σ + t I) ≠ 0) (σ : ℝ) : xi (σ + t I) ≠ 0
```
S1R (`SchoenfeldS1.R`), the rectangle half of (C):
```
xi_ne_zero_frontier (hord : NotOrdinate T) : ∀ x ∈ frontier (Rectangle (-1) (2 + T I)), xi x ≠ 0
filter_zerosBandF_eq (hT : 0 < T) : (zerosBandF (-1) (T+1)).filter (· ∈ Rectangle (-1) (2 + T I)) = zerosBandF 0 T
sum_order_xi_eq_NT (hT : 0 < T) : Σ_{s ∈ zerosBandF (-1) (T+1), s ∈ Rectangle} (analyticOrderNatAt xi s : ℂ) = NT T
theorem rect_arg_sub_eq_two_pi_mul_NT (hT : 0 < T) (hord : NotOrdinate T) {θ : ℝ → ℝ}
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc 0 4, xi (rectBoundary (-1) (2 + T I) t) = ‖xi (…)‖ exp (I θ t)) :
    θ 4 - θ 0 = 2 π NT T
```
(Tau Ceti `argumentPrinciple_rectBoundary_of_analyticOnNhd` on `U = (-2,3) × (-1, T+1)`, finite zero
set `zerosBandF (-1) (T+1)`, and
`AbsolutelyContinuousOnInterval.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub`.)

### Compiled modulo one `sorry` (S1C_WIP, imports B, D3, G, Z)

The WIP file now type-checks with exactly one `sorry`, `NT_eq_rsTheta_add`; everything downstream
is proven from it:
```
theorem NT_eq_rsTheta_add (hT : 14 ≤ T) (hord : NotOrdinate T) : (NT T : ℝ) = rsTheta T / π + 1 + riemannZetaS T  -- SORRY
lemma Mt_eq_rsThetaMain (hT : 0 < T) : Mt T = rsThetaMain T / π + 1
theorem abs_NT_sub_Mt_le (hT : 14 ≤ T) (hord : NotOrdinate T) : |(NT T : ℝ) - Mt T| ≤ RtB T
lemma continuousAt_Mt, continuousAt_RtB (hT : 0 < T)
theorem NT_le_Mt_add_RtB (hT : 14 ≤ T) : (NT T : ℝ) ≤ Mt T + RtB T          -- (U'), all T ≥ 14
theorem Mt_sub_RtB_le_NT (hT : 1000 ≤ T) : Mt T - RtB T ≤ NT T              -- (L'), all T ≥ 1000
theorem schoenfeld_psi_large_of_Z (h14 : NT 14 = 0) : ∀ x ≥ 10^15, |ψ x - x| ≤ √x log² x/(8π)
theorem schoenfeld_psi : ∀ x ≥ (10:ℝ)^15, |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 / (8 * π)
theorem schoenfeld_theta : ∀ x ≥ (10:ℝ)^15, |Chebyshev.theta x - x| ≤ √x * Real.log x ^ 2 / (8 * π)
```
(U')/(L') at ordinates: filters `𝓝[>] T`, `𝓝[<] T`; `Filter.eventually_all_finset` over
`zerosBandF T (T+1)` (resp. `zerosBandF (T-1) T`) gives that every `T'` close to `T` is a
non-ordinate with `NT T' = NT T` (resp. `NT T' ≤ NT T`); `ge_of_tendsto`/`le_of_tendsto` with the
continuity of `Mt ± RtB`. No separate `exists_notOrdinate_between` was needed.

### What remains for `NT_eq_rsTheta_add` (the boundary argument, S1R second half)

With `rect_arg_sub_eq_two_pi_mul_NT` the identity is: for some continuous argument `θ` of `xi`
along `rectBoundary (-1) (2 + iT)`, `θ 4 - θ 0 = 2 (π + rsTheta T + π S(T))`. Plan (verified by hand):
1. **Arg of `xi` along the L-path** `p u := riemannZetaSPath T u`, `u ∈ [0, 2]`:
   `xi (p u) = p u (p u - 1) · Gammaℝ (p u) · ζ (p u)` (`xi_eq_mul`; `Re p u ≥ 1/2`). Polar forms:
   * `s (s - 1) = ‖s‖‖s - 1‖ e^{i (arg s + arg (s - 1))}` (`norm_mul_exp_arg_mul_I`), both `s` and
     `s - 1` in `slitPlane` along the path (`Im > 0` or real `> 0`), so `α u := arg (p u) + arg (p u - 1)`
     is continuous (`continuousAt_arg`), `α 0 = 0`, `α 2 = arg (1/2 + iT) + arg (-1/2 + iT) = π`
     (`arg_of_re_neg_of_im_nonneg`, `arg` of `Re > 0` is `arctan (im/re)`).
   * `Gammaℝ s = exp (-(s/2) log π + logGamma (s/2))` (`cpow_def_of_ne_zero`, `TauCeti.exp_logGamma`,
     `s/2 ∈ slitPlane`), so `β u := -(Im p u)/2 · log π + Im (logGamma (p u / 2))` is continuous
     (`differentiableOn_logGamma.continuousOn`), `β 0 = 0` (`logGamma_one`), `β 2 = rsTheta T`
     (`zTheta T = (1/2 + iT)/2`).
   * `φ` from `exists_riemannZetaS_eq_div_pi`: `φ 0 = 0`, `φ 2 = π S(T)`.
   `Θ u := α u + β u + φ u` is a continuous argument of `xi ∘ p` on `[0, 2]`, `Θ 0 = 0`,
   `Θ 2 = π + rsTheta T + π S(T)`.
2. **The five cells of `rectBoundary (-1) (2 + iT)`** (`rectBoundary_of_mem_Icc_*`):
   `[0,1]` bottom `-1 + 3t` (arg `0`, `xi_ofReal_pos`); `[1,2]` right `= p (t - 1)` (arg `Θ (t-1)`);
   `[2, 5/2]` top-right `= p (1 + 2(t-2))` (arg `Θ (2t - 3)`); `[5/2, 3]` top-left
   `xi = conj (xi (p (7 - 2t)))` by `xi_one_sub` and `xi_conj` (arg `-Θ (7 - 2t)`); `[3,4]` left
   `xi (-1 + i T(4-t)) = conj (xi (p (4 - t)))` (arg `-Θ (4 - t)`). Cell changes
   `0, Θ 1, Θ 2 - Θ 1, Θ 2 - Θ 1, Θ 1`, total `2 Θ 2`.
3. **Uniqueness per cell**: Tau Ceti `sub_eq_sub_of_eq_norm_mul_exp` (two continuous arguments of
   the same nonvanishing function on a preconnected set have the same variation) applied to the
   restriction of the global `θ` (from `exists_continuousOn_eq_norm_mul_exp_rectBoundary`) and the
   explicit cell argument, cell by cell; telescoping gives `θ 4 - θ 0 = 2 Θ 2`, then
   `2 π NT T = 2 (π + rsTheta T + π S(T))`.
Estimated 6 to 10 h (casts and the five cell parametrizations are the cost, no new mathematics).

### S1L_WIP (step 1 of the remaining plan, 15:35): `exists_arg_xi_path`, nearly compiled

`S1L_WIP_v1.0_11-27-2026.lean` (imports X, D3, B) states and proves
```
theorem exists_arg_xi_path (hT : 14 ≤ T) (hord : NotOrdinate T) : ∃ Θ : ℝ → ℝ, ContinuousOn Θ (Icc 0 2) ∧
    (∀ u ∈ Icc 0 2, xi (riemannZetaSPath T u) = ‖xi (…)‖ exp (I Θ u)) ∧ Θ 0 = 0 ∧ Θ 2 = π + rsTheta T + π riemannZetaS T
```
with `Θ u = arg (p u) + arg (p u - 1) + (wG (p u)).im + φ u`, `wG s = log π · (-s/2) + logGamma (s/2)`.
Compiled pieces: `polar_mul`, `polar_of_arg`, `polar_exp`, `re_path_ge`, `im_path_nonneg`,
`path_mem_slitPlane`, `path_sub_one_mem_slitPlane`, `continuousOn_path`, `polar_quad`,
`continuousOn_argQuad`, `argQuad_two` (`arg(1/2 + iT) + arg(-1/2 + iT) = π`), `Gammaℝ_eq_exp_wG`,
`polar_Gammaℝ`, `wG_two_im`, `wG_half_add_im` (`= rsTheta T`), and the main theorem's four goals
(the polar product and the two endpoint values go through). Two defects left (last check, 21 s):
1. `argQuad_zero` (`arg 2 + arg 1 = 0`): `rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num]` already closes
   the goal, so the following `exact` reports "no goals"; drop the `exact` lines.
2. `continuousOn_wG : ContinuousOn wG {s | 0 < s.re}` hits a `whnf` heartbeat timeout even at
   `maxHeartbeats 1000000` (likely the elaboration of `continuousAt_id.neg.div_const 2` against
   `fun s => ↑(log π) * (-s / 2)`, or the set-builder membership `hs`); rewrite it with explicit
   `HasDerivAt`/`Continuous` lemmas or `ContinuousOn.add` on named functions, or prove
   `ContinuousOn (fun s => (wG s).im)` through `Complex.continuous_im.comp_continuousOn`
   with the two summands separately.
Everything else in the file elaborates (the "unknown constant" kernel message is a consequence of 2).

### NEXT-CHUNK plan (chunk 4), in order
1. Fix the two S1L defects (30 min), build `SchoenfeldS1.L`, `#print axioms`.
2. The five cells (S1R second half, 4 to 8 h): for each cell of `rectBoundary (-1) (2 + iT)` give the
   explicit continuous argument (see "What remains" above), prove the cell lift
   (`rectBoundary_of_mem_Icc_*`, `xi_one_sub`, `xi_conj`, `xi_ofReal_pos`), then apply
   `TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp` to the global `θ` from
   `exists_continuousOn_eq_norm_mul_exp_rectBoundary` (`continuous_xi.continuousOn`,
   `xi_ne_zero_frontier`) and telescope: `θ 4 - θ 0 = 2 Θ 2`. With `rect_arg_sub_eq_two_pi_mul_NT`
   this is `NT_eq_rsTheta_add` (divide by `2π`).
3. Move `NT_eq_rsTheta_add` and the S1C_WIP glue into delivered `S1C`/`S1H` files, build, axioms,
   grep rules, mirror. Then `schoenfeld_psi`/`schoenfeld_theta` are unconditional.
4. Optional tightening (`x₀ = 10^14`, Backlund's `0.137`) as before.

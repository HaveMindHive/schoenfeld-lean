# PROGRESS: ExplicitRH (11-27-2026), milestone F1 - COMPLETE

File: `ExplicitRH_v1.0_11-27-2026.lean` (1723 lines, namespace `WallsMeetRHExplicit`), no `sorry`,
no `admit`, no `native_decide`. Imports `WallsMeetRHVonKoch` (compiled to an olean in `build/` by the
check script, wings pattern) for the wall section, the contour identity and the residue lemma.
Check: `./check-explicit_v1.0_11-27-2026.sh`; output `check-explicit-output_v1.0_11-27-2026.txt`:
zero errors, zero warnings, every `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Credit: RH by Alpoge with Claude (community condensed proof, `riemannHypothesis` in `Main`); wall
count = `Nat.primeCounting` by Rayn-McLean's `prime_count_walls`. Tau Ceti (Apache-2.0, The Tau Ceti
contributors): private lemmas of `Window.lean` and `Local.lean` copied or adapted, attributed in place.
Component files (compiled standalone, then inlined as sections): `ExplicitBump_v1.0_11-27-2026.lean`,
`ExplicitSafeHeight_v1.0_11-27-2026.lean`, `ExplicitZeroSum_v1.0_11-27-2026.lean`.

## Final statements (all numerals)
- `psi_sub_le_explicit : ∀ x : ℝ, 55 ≤ x → |ψ x - x| ≤ 21250000000 * √x * Real.log x ^ 2`
- `theta_sub_le_explicit : ∀ x ≥ 55, |θ x - x| ≤ 21250000006 * √x * Real.log x ^ 2`
- `primeCounting_sub_logIntegral_le_explicit : ∀ x ≥ 55, |π ⌊x⌋₊ - Li x| ≤ 913750000391 * √x * log x`
- `walls_meet_rh_explicit : ∀ N : ℕ, 55 ≤ N → |(2 + #{n ≤ N | passes n} : ℝ) - Li N| ≤ 913750000391 * √N * log N`

## Where the numerals come from
- `norm_LFunctionTrivChar₁_one_le_pow_mul`: `‖(w-1)ζ(w)‖ ≤ (|t|+2)^9 ‖(s₀-1)ζ(s₀)‖` on `‖w - (2+it)‖ ≤ 31/16`
  (Re w ≥ 1/16; Tau Ceti `norm_riemannZeta_le_of_re_pos` gives `≤ 1 + (τ+1)(1+16(τ+2)) ≤ 49 τ²`; centre
  `‖ζ(2+it)‖ > 1/2` from `inv_norm_riemannZeta_lt_one_add_one_div_sub_one`; `98 ≤ τ^7`).
- `count_zeros_disc_le`: zeros in the disc of radius `29/16` about `2+it` number `≤ 140 log(|t|+2)`
  (Jensen `sum_divisor_le_log_div_log`: `9 log τ / log(31/29)`, `log(31/29) ≥ 2/31`).
- `logDeriv_window_explicit`: window form constant `33413 = 3697·9 + 140` (Landau's factor at
  `d ≤ 7/4`, radii `29/16 < 31/16`: `4(29/16+d)/(29/16-d)² ≤ 3648`, second term `≤ 49`).
- `logDeriv_bound_explicit`: `‖ζ'/ζ + 1/(s-1)‖ ≤ 33553/a · log(|Im s|+2)` at distance `a` from `1/2`,
  `1/4 ≤ Re s ≤ 2` (`33553 = 33413 + 140`).
- `riemannZeta_safe_height_of`: `Cs = 2|Cw| + 288 Cc² + 24|Cc| + 1`; at `Cw = 33413, Cc = 140`:
  `Cs = 5714987` (six discs of radius 29/16 cover the two windows, `K ≤ 12 Cc log(T+2)`, pigeonhole).
- `sum_order_div_norm_le_of`: `∑ m(ρ)/|ρ| ≤ 32 Cc log²(T+2)`, `Cz = 4480`.
- `exists_explicit_bump`: `ν = (max 0 ((x-1/2)(2-x)))² / m₀`, `‖𝓜χ_ε(s)‖ ≤ 168/(|s|(1+ε|s|))`
  (pointwise `243/64`, integration by parts `81/8`, mass `m₀ ≥ 1/12`).
- Von Koch assembly (same body as `psi_sub_le_sqrt_log_sq`): `C₀ = 16e·168 + (64·33553+11)·168 +
  8e·5714987·168 + 4·168·4480 + 11 ≈ 2.1243 × 10^10 ≤ 21250000000` (`e < 2.7182818286`).
- θ: `+6`. π: `133 + 43 K` with `|π(55) - Li 55| ≤ 56 + 77 = 133`, `K √55 log 55 ≤ 40 K`.

## Distance to Schoenfeld (1/(8π) √x log² x, x ≥ 73.2; π: √x log x/(8π), x ≥ 2657)
Constant ratio about `5 × 10^11`. Dominant term `8e·Cs·C` with `Cs ∝ Cc²` (the pigeonhole safe height
pays `K(K+1)`) and `Cc = 140` (Jensen on discs confined to Re > 0, ratio `31/29`). To close the gap:
(1) a sharp zero count `N(T+1) - N(T) ≤ (1/2π) log T + O(1)` from the Riemann-von Mangoldt formula
(argument principle on the completed zeta, Stirling), none of which is explicit in Lean yet;
(2) replace the safe-height `K²` by the standard `∑ 1/|T' - γ| ≪ log² T` with `T'` chosen at
distance `≫ 1/log T` and use `∑_ρ |x^ρ/ρ|` with the explicit `N(T)` (Schoenfeld's `∑ 1/|ρ|` tail);
(3) the sharp (not smoothed) Perron formula with the explicit `R(x, T)` error, removing the Mellin
constant `168` and the `log 2` smoothing loss;
(4) small x: Schoenfeld's `x ≥ 73.2` needs numerical verification of ψ below the analytic range,
which this file avoids by taking `x ≥ 55` where `log x ≥ 4` makes every term `≤ √x log² x` times its
constant.

## Remaining
Nothing for F1. No WIP file needed.

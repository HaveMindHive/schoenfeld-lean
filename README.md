# schoenfeld-lean

> **Proven, with nothing assumed beyond the proven Riemann hypothesis:** for every x ≥ 10¹⁵,
> |ψ(x) − x| ≤ √x·(log x)²/(8π) and |θ(x) − x| ≤ √x·(log x)²/(8π),
> Schoenfeld's exact constant, kernel-checked in Lean 4 (`SchoenfeldS1.schoenfeld_psi`, `SchoenfeldS1.schoenfeld_theta`; axioms: `propext`, `Classical.choice`, `Quot.sound`; see `S1-zero-counting/axioms-final_v1.0_11-27-2026.txt`).

An open project to formalize in Lean 4 **Schoenfeld's explicit prime bounds**, which are now unconditional because the Riemann hypothesis is proven:

- |ψ(x) − x| < √x·(log x)² / (8π) for x ≥ 73.2
- |θ(x) − x| < √x·(log x)² / (8π) for x ≥ 599
- |π(x) − li(x)| < √x·log x / (8π) for x ≥ 2657

(L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30 (1976); re-proved by J. Büthe, arXiv:1410.7015, with ψ from x > 59.)

Every file is kernel-checked inside the environment of the community Lean proof of the Riemann hypothesis ([leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), proof by Levent Alpöge with Claude), from its `riemannHypothesis : RiemannHypothesis`, with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Led by Turaq Rayn-McLean, with Anthropic's Claude.

## Roadmap

| Stage | Target | Status |
|---|---|---|
| **0** | Square-root bounds with an unnamed constant: ψ(x) − x = O(√x·(log x)²), π(x) − Li(x) = O(√x·log x) (von Koch), via a kernel-checked truncated explicit formula | done (see [rh-consequences](https://github.com/HaveMindHive/rh-consequences)) |
| **F1** | The same with explicit numerals | **done**: \|ψ(x) − x\| ≤ 21250000000·√x·(log x)² and \|π(x) − Li(x)\| ≤ 913750000391·√x·log x for every x ≥ 55 (`WallsMeetRHExplicit` in `F1-explicit/`, standard axioms). About 5·10¹¹ times Schoenfeld's 1/(8π): explicit, not yet sharp |
| **S2** | Schoenfeld's exact ψ and θ forms for x ≥ 10¹¹, from RH plus three explicit zero-count statements (port of goldbach-lean's `psi_schoenfeld_large`) | **done**: `SchoenfeldPort.schoenfeld_psi_large`, `schoenfeld_theta_large` in `S2-schoenfeld-large/` (50 modules, 9,824 lines, RH discharged by `riemannHypothesis`, standard axioms) |
| **S1** | Prove the zero statements | **done**: no zero with 0 < Im ρ ≤ 14 (certified Euler–Maclaurin), the Riemann–von Mangoldt identity N(T) = θ(T)/π + 1 + S(T) by the argument principle (`NT_eq_rsTheta_add`), Backlund's \|S(T)\| ≤ 4.5 log T + 17.08, hence N(T) within Mt ± (4.5 log T + 17.1), and S2 retuned to absorb these constants from x ≥ 10¹⁵. Result: `schoenfeld_psi`, `schoenfeld_theta` |
| **S3** | Lower the start from 10¹⁵ (sharper zero counting, e.g. Backlund's 0.137 via convexity) | open |
| **S4** | Certified computation for the remaining small range (down to 73.2 / 599 / 2657) | open |
| **S5** | θ and π transfers to the exact Schoenfeld forms, with li (not Li, which differs by li(2) ≈ 1.045) | open |
| **S6** | **Ramanujan's inequality**, π(x)² < (e·x/ln x)·π(x/e), for every x > 38,358,837,682: known under RH (Dudek–Platt), so a theorem now that RH is proven. Uses the explicit π bounds above plus computation for the middle range | open (flagship application) |

## Where it stands

- **Done and kernel-checked:** von Koch's square-root bounds (stage 0); the first fully explicit bounds from the proven RH, |ψ(x) − x| ≤ 21250000000·√x·(log x)² and |π(x) − Li(x)| ≤ 913750000391·√x·log x for every x ≥ 55 (F1); and **Schoenfeld's exact constant 1/(8π) for ψ and θ for every x ≥ 10¹¹**, from the proven RH plus three explicit statements about the zeros of ζ (S2).
- **Done (S1):** the three zero statements, so Schoenfeld's ψ and θ bounds hold for every x ≥ 10¹⁵ from the proven RH alone.
- **Next:** bring the start down toward 73.2 / 599 (S3, S4), the π form with li (S5), and Ramanujan's inequality (S6). Help is welcome (see the issues).

## Check it

You need a built clone of `leanprover-community/riemann-hypothesis` (tested at commit `8c828ed`, Lean v4.37.0-rc1). F1: `F1-explicit/check-explicit_v1.0_11-27-2026.sh` (see its header). S2: build the ported modules with the scripts in `S2-schoenfeld-large/tools/`, then `RH_REPO=/path/to/riemann-hypothesis sh S2-schoenfeld-large/tools/lean1_v1.0_11-27-2026.sh S2-schoenfeld-large/src/SchoenfeldPort/Final.lean`. Every main theorem ends with `#print axioms`; expect `[propext, Classical.choice, Quot.sound]`.

## Credits and licence

Riemann hypothesis: Levent Alpöge with Claude, condensed by the Lean community. Tau Ceti, goldbach-lean (sthubbar) and PrimeNumberTheoremAnd: see `NOTICE`. Apache-2.0.

# schoenfeld-lean

A Lean 4 formalization of **Schoenfeld's explicit prime bounds**, now unconditional because the Riemann hypothesis is proven:

- |ψ(x) − x| < √x·(log x)² / (8π) for x ≥ 73.2
- |θ(x) − x| < √x·(log x)² / (8π) for x ≥ 599
- |π(x) − li(x)| < √x·log x / (8π) for x ≥ 2657

(L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30 (1976); re-proved by J. Büthe, arXiv:1410.7015, with ψ from x > 59.)

Every file is kernel-checked inside the environment of the community Lean proof of the Riemann hypothesis ([leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), proof by Levent Alpöge with Claude), from its `riemannHypothesis : RiemannHypothesis`, with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Led by Turaq Rayn-McLean, with Anthropic's Claude.

## Roadmap

| Stage | Target | Status |
|---|---|---|
| **0** | Square-root bounds with an unnamed constant: ψ(x) − x = O(√x·(log x)²), π(x) − Li(x) = O(√x·log x) (von Koch), via a kernel-checked truncated explicit formula | done (see [rh-consequences](https://github.com/HaveMindHive/rh-consequences)) |
| **F1** | The same with explicit numerals: \|ψ(x) − x\| ≤ C₀·√x·(log x)² for x ≥ X₀ | in progress |
| **S2** | Schoenfeld's exact ψ and θ forms for x ≥ 10¹¹, from RH plus three explicit zero-count statements (port of goldbach-lean's `psi_schoenfeld_large`) | in progress |
| **S1** | Prove those zero-count statements: an explicit Riemann–von Mangoldt bound for N(T), and no zero below height 14 | open |
| **S3** | Lower the analytic start from 10¹¹ | open |
| **S4** | Certified computation for the remaining small range (down to 73.2 / 599 / 2657) | open |
| **S5** | θ and π transfers to the exact Schoenfeld forms, with li (not Li, which differs by li(2) ≈ 1.045) | open |

## Credits and licence

Riemann hypothesis: Levent Alpöge with Claude, condensed by the Lean community. Tau Ceti, goldbach-lean (sthubbar) and PrimeNumberTheoremAnd: see `NOTICE`. Apache-2.0.

# Finite theta certificate for [599, 613]

`SchoenfeldThetaInterval.theta_599_613` proves the strict Schoenfeld bound for every real point of the closed interval, including the prime endpoints. It imports Mathlib and has no RH premise.

The proof bounds the primorial at 599, 601, 607 and 613 using powers of two. A small recursive product tests primality via the least prime factor. Its equality to Mathlib's primorial is proved by induction. The kernel evaluates the integer comparisons. Monotonicity of θ then gives an error below 38.5 on each subinterval. The analytic bound exceeds 38.5 throughout. The shared endpoints allow adjoining a subsequent interval starting at 613.

To check the file, set `cert` to its absolute path and run the following from a built Lean project with Mathlib at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (Lean `v4.37.0-rc1`, the dependencies used by S1).

```sh
lake env lean -j1 -DwarningAsError=true "$cert"
{ cat "$cert"; echo '#print axioms SchoenfeldThetaInterval.theta_599_613'; } | lake env lean -j1 --stdin
```

The expected axiom set is `propext`, `Classical.choice` and `Quot.sound`.

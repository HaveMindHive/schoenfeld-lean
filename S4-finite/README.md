# Finite theta certificate for [599, 1024]

`SchoenfeldThetaInterval.theta_599_1024` proves the strict Schoenfeld bound for every real point of the closed interval, including both endpoints and all prime jumps. It imports Mathlib and has no RH premise.

The original lemma covers [599, 613]. The extension proves [613, 1024] using 35 right endpoints. Each adjacent pair bounds θ by monotonicity and the binary lengths of the endpoint primorials. The kernel checks both errors against a rational lower bound on the Schoenfeld allowance. A proof that the checker covers every real point joins the intervals, including 613.

The source file retains its original name, `Theta599To613.lean`. It exports the three lemmas `theta_599_613`, `theta_613_1024` and `theta_599_1024` in the `SchoenfeldThetaInterval` namespace.

To check the file, set `cert` to its absolute path and run the following from a built Lean project with Mathlib at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (Lean `v4.37.0-rc1`, the dependencies used by S1).

```sh
lake env lean -j1 -DwarningAsError=true "$cert"
{ cat "$cert"; echo '#print axioms SchoenfeldThetaInterval.theta_599_1024'; } | lake env lean -j1 --stdin
```

The expected axiom set is `propext`, `Classical.choice` and `Quot.sound`.

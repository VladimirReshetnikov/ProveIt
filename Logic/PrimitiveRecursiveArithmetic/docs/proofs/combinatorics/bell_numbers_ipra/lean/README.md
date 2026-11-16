# Lean status

Tested with Lean 4.32.0. Only Lean's bundled `Std` library is needed.

```sh
bash check.sh
```

If the compiler is outside `PATH`, set `LEAN_BIN` to its absolute path.
Generated objects and logs go to `build/`, or to `BELL_BUILD_DIR` if set.

## What is proved

`BellCore.lean` defines finite sums, Stirling numbers, Bell numbers and
factorials, then proves:

- finite-sum addition, shift, monotonicity and scalar multiplication;
- vanishing of S(n,k) for k>n, diagonal S(n,n)=1 and S(n+1,1)=1;
- the weighted Bell recurrence B(n+1)=sum_{k<=n}(k+1)S(n,k);
- positivity, monotonicity, B(n+1)<=(n+1)B(n), and B(n)<=n!;
- the values B(0),...,B(10), by definitional reduction.

These are Lean metatheorems about natural-number functions. They are not
`ConciseIPRA.Prf` derivations and should not be advertised as a complete
formalization in iPRA.

## What is specified

`BellTargets.lean` supplies total rational-code programs for exp, log, W,
square root and pi; a mixed-radix first-order Bell program; an explicit
growth modulus; and proposition definitions for the remaining exact and
asymptotic targets. A definition named `...Target` is an unproved goal,
not a theorem or an added axiom. No `sorry` or `axiom` declarations are used.

The mathematical approximation bounds and all requested human proofs are in
the accompanying paper. The target programs prioritize a transparent PR
bound over practical numerical efficiency; in particular the rational
truncations and dyadic W search can be exceptionally large.

`Audit.lean` prints trusted-axiom reports for the proved theorems. The reports
in `verification/lean-axioms.txt` distinguish axiom-free computational facts
from proofs using Lean's `propext` and `Quot.sound`. No report contains
`Classical.choice` or `sorryAx`.

## ProveIt integration

The paper pins and audits the repository at
`c0d0dc37f60aea10c0182ba4eece9eae8c7e13c6`. It identifies the required
`PR`, `PTm`, `Fm`, `PRAAx`, `PRA.qfInd`, `Prf` and translation interfaces.
The final integration work is to emit fixed PR codes for the programs and
construct derivations of the finite arithmetic lemmas with `PRA.qfInd`.
The existing bi-interpretation then transports those constructed derivations
to the concise calculus. It does not construct Bell proofs automatically.

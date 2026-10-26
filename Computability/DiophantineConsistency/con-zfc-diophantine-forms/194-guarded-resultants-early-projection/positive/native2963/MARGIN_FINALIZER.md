# Package 52's margin-first finalizer

The checked arithmetic in
[`MarginFinalizer.lean`](Lean/DiophantineConsistency/MarginFinalizer.lean)
matches Section 5 of package 52's nine-variable proof. Put

```
Omega = J*m
Theta = J*n+Q-Omega*(V0+V1)
F9 = (Theta^2-Omega^2*(a0+64*a1))^2-256*Omega^4*a0*a1.
```

The theorem `exists_value_zero_iff` proves that a natural `n` with `F9=0`
exists exactly when `a0` and `a1` are integer squares, `J` divides `Q`, and
`m>0`. Its hypotheses are explicit:

* nonnegative radicands and positive `V0,V1,J,Q`;
* unconditional strict majorants `a0<V0^2` and `64*a1<V1^2`;
* `Q<V1`;
* the conditional bound `m>0 -> a0<64*a1`.

The proof recovers `m>0` first. An integer inequality shows that a
nonpositive `Omega` and positive `J*n+Q` place `Theta` strictly outside
the sum of the two majorants, forcing the norm to be positive. This is
an algebraic version of the report's real-root bound and assumes no
integrality of the radicals. Only after recovering the margin does
separation exclude the zero root sum. Rational reconstruction and the
rational-square-root theorem then produce signed integer roots.

Completeness chooses nonnegative integer roots and constructs
`n=m*(V0+V1+r0+8*r1)-Q/J`. The bound `Q<V1` proves this is natural;
`Q` may exceed `J`. The polynomial data use no division or root operation.

[`MarginSeparation.lean`](Lean/DiophantineConsistency/MarginSeparation.lean)
proves the concrete arithmetic bounds behind those hypotheses. In
particular, the actual margin
`(K^2-4*(C-K*Y)^2)*cap-8*g*K^2` forces `C>K`, already for `Y>=2`.
The Pell-register identities give `P<A^2`, `D>C^2`, `F>=A^2`, and
`I>=A^2`, hence `a0=(P^2-1)*K^2+1<D*F*I=a1` on that branch.
The concrete `Q=3*W*C-2*(W^2-1)` is positive and below `3*C^2`,
which is below the second majorant `k*(8*D^2-4*D-1)*G*H`.

[`RatioMarginFinalizer.lean`](Lean/DiophantineConsistency/RatioMarginFinalizer.lean)
combines these bounds with the checked second-majorant defect identity
from `NearSquareFinalizer.lean`. Its `exists_value_zero_iff` assumes the
displayed Pell-register identities and primitive positivity/range bounds,
and derives all separation and majorant obligations. It retains precisely
the package-52 four-condition result.

The three modules and their files in `Lean/checks/` compile without proof
placeholders or new axioms. Checks cover all four signed-root branches,
zero and negative margins, failed divisibility, a nonsquare radicand,
and the equal-radicand counterexample excluded by the separation hypothesis.
Their axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
These theorems establish the finalizer stage; the source compiler and
calibration to ZFC refutations remain separate theorems.

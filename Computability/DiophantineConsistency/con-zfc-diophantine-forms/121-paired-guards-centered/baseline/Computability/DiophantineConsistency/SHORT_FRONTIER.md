# A second tradeoff: 73 operations and degree 80

[`circuits/p73_sos.json`](circuits/p73_sos.json) evaluates an ordinary
fifteen-variable polynomial using **73 operations**: 41 multiplications,
17 additions, and 15 subtractions. Its exact total degree is **80** for the
prescribed coefficient tuple. Every gate and input port is used.

This is an alternative to the [75-operation, degree-68 equation](SHORT_SYSTEM.md).
Both have the complete positive zero set of the report's P67, at the same
coordinates. The new Lean certificates prove these local algebraic
equivalences. They do not certify the native-window compiler or supply an
end-to-end Con(ZFC) equivalence for these small explicit circuits.

Use the same fifteen positive unknowns, four fixed coefficient ports, whole
coefficient tuple, and factor definitions `N0,N1,Na,Nk,Nt,Ns` as in
[SHORT_SYSTEM.md](SHORT_SYSTEM.md). The new equation is

```
(N0*N1-1)^2 + (Na*Nk*Nt-1)^2 + (Ns-1)^2 = 0.
```

At a product zero, the factor classification already checked in
`ShortSystem.lean` gives `N0=N1=Na=Ns=1` and `Nk*Nt=1`, hence all three grouped
residuals vanish. Conversely, the vanishing sum of squares sets each group
product to one. Multiplying the three group equations recovers the original
unit-product equation. No additional factor-sign assumptions are needed.

The DAG retains 62 live producers from P69 after removing the final product
gates and the obsolete `norm_pair` and `norm_strong` gates. It reuses `f^2-1`
to compute `Ns-1`. Three group multiplications, three residual subtractions,
three squares, and two additions finish the equation: `62+3+3+3+2 = 73`.

The three residuals have degrees 40, 37, and 34, respectively. The degree-18
main norm uses the exact cancellation

```
(a*c+X+g)^2-(a^2+H)*c^2
  = X^2+2*a*c*(X+g)+2*X*g+g^2-H*c^2.
```

With degrees `a=6,c=5,X=2,g=7,H=6`, the right side has degree at most 18.
Both the finite audit and the Lean degree certificate check this identity.
Only the first residual's square reaches degree 80. Its leading homogeneous
form is

```
64*gamma^2*w^8*s^14*(eta+zeta)^6*(beta*J)^50.
```

Thus the coefficient of `J^50*eta^6*gamma^2*w^8*s^14` is `64*beta^50`, which
is nonzero when `beta != 0`. The exact lower degree is established by the
finite audit; Lean checks the upper bound of 80 independently.

[`ShortFrontier.lean`](Lean/DiophantineConsistency/ShortFrontier.lean)
defines the actual `MvPolynomial (Fin 15) ℤ`, checks its equality to the
literal 73-gate evaluator, proves its degree bound, and proves its complete
positive-zero equivalence to P67. Its audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

```sh
python3 Computability/DiophantineConsistency/tools/build_frontier_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_frontier_circuit.py
lake build DiophantineConsistency.ShortFrontier
```

The deterministic ledger is
[`circuits/p73_sos.audit.json`](circuits/p73_sos.audit.json). The auditor uses
only Python's standard library, shares sparse-polynomial arithmetic primitives
with the independent P75 auditor, and independently checks the P73 gate matrix,
liveness, counts, cancellation identity, homogeneous form, and provenance.
These are two useful tradeoffs within the investigated constructions; no
global optimality is claimed.

# Fifteen positive variables, 76 operations, degree 64

The literal circuit [`circuits/p76_sos.json`](circuits/p76_sos.json) uses the
same fifteen positive unknowns and the same four coefficient ports as P75.
Its complete positive zero set agrees with the pinned P67 circuit. This
adds a degree/operation tradeoff: P73 has degree 80, P75 degree 68, and P76
degree 64. No minimality or priority claim is made.

The proof is in
[`ShortReducedStrong.lean`](Lean/DiophantineConsistency/ShortReducedStrong.lean).
It does not supply the native-window compiler or independently prove that
these short candidates encode ZFC refutations. The separate
primitive-recursion/Jones construction has a supplied-program interface;
its concrete refutation-program data are still being constructed.

## Equation and exact zero equivalence

Keep all abbreviations and coordinate conventions of
[`SHORT_SYSTEM.md`](SHORT_SYSTEM.md). In particular, put

```
r0 = N0-1,
R  = f^2-1 - (i^2*c^2)*(Delta*c^2+r0).
```

The new equation is

```
r0^2 + (Na-1)^2 + R^2 + (N1*Nk*Nt-1)^2 = 0.
```

This equation and P75 have exactly the same zeros over all integer
assignments, for arbitrary integer coefficient ports. At any zero, the
first square forces `r0=0`, after which `R=Ns-1`. Conversely every P75 zero
has `r0=0` and makes the new residual equal its old strong residual. No
positivity argument is needed for this triangular change. Positivity and
positive `beta` enter only when using the existing P75-to-P67 theorem.

The Lean APIs are:

* `value_zero_iff_compactValue_zero`: complete integer zero equivalence;
* `literalValue_eq_value`: the literal DAG equals the displayed expression;
* `eval_polynomial_zero_iff_baselineValue_zero`: positive zero equivalence
  for the actual `MvPolynomial (Fin 15) ℤ`;
* `polynomial_totalDegree_le`: kernel-checked total degree at most 64.

## Why the degree falls

Write `X=w*q`, `Y=s*q^3`, `k=eta+zeta`, and `c=k*Y+eta`. Then
`a=X*Y+Y`, `Delta=a^2+4*a+3`, and
`N0=tau^2-(X*Y^2)*(X*Y^2+1)*k^2`. The inner correction obeys the exact
polynomial identity

```
Delta*c^2 + N0-1
 = ((2*X+1)*Y^2 + 4*a+3)*c^2
   + (X*Y)^2*eta*(2*k*Y+eta)
   - X*Y^2*k^2 + tau^2-1.
```

The first expression's apparent degree 22 cancels to degree 20. Multiplying
by `i^2*c^2`, of degree 12, gives a strong residual of degree 32. The other
squared residuals have degrees 44, 56, 54 respectively, so the corrected
strong square determines degree 64. The Lean bound uses an explicit ring
identity and degree arithmetic for the actual polynomial.

The independent sparse audit expands the corrected factor's 238 terms and
checks the cancellation. It verifies the final leading homogeneous form

```
4*i^4*(eta+zeta)^8*w^2*s^12*(beta*J)^38.
```

In particular, the monomial `J^38*i^4*eta^8*w^2*s^12` has coefficient
`4*beta^38`, which is nonzero for positive `beta`. Thus the stated degree 64
is exact on the intended coefficient slice. The matching lower-degree
claim is an independent finite symbolic audit; Lean proves the upper bound.

## Paid circuit and reproducibility

P75 uses three multiplications for `(i*c^2)^2*Delta`. P76 instead computes
`i^2`, `i^2*c^2`, `Delta*c^2+r0`, and their product. The factor `Delta*c^2`
and the first residual are already available. Therefore the replacement
adds exactly one addition. The final count is 41 multiplications,
19 additions and 16 subtractions: 76 binary arithmetic operations.

Run from the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_reduced_strong.py
python3 Computability/DiophantineConsistency/tools/audit_reduced_strong.py
```

The generator emits the JSON and literal Lean/degree certificates only in
this new module. The independent stdlib audit checks all operands,
coordinate and coefficient bindings, source hashes, every gate's
liveness, the operation count and exact leading form. Its saved ledger is
[`circuits/p76_sos.audit.json`](circuits/p76_sos.audit.json).

The Lean correctness and degree theorems audit with only `propext`,
`Classical.choice`, and `Quot.sound`; no additional axioms or `sorry` are
introduced.

Further scalar residual shears and their limited degree obstruction are
recorded in [RESIDUAL_SHEAR_SEARCH.md](RESIDUAL_SHEAR_SEARCH.md), with a
reproducible exact search. They do not yield a lower-cost degree-64 circuit.

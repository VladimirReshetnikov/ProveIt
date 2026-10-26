# A degree-68 polynomial with 75 arithmetic operations

The equation in [`circuits/p75_sos.json`](circuits/p75_sos.json) has fifteen
strictly positive integer unknowns and four fixed coefficient ports. Its
complete division-free evaluation uses **75 operations**: 41 multiplications,
18 additions, and 16 subtractions. Every gate and input port is used. Its exact
total degree in the unknowns is **68** when `beta != 0`.

Lean proves that the actual fifteen-variable polynomial has precisely the
positive zeros of the report's P67 at the same coordinates. This is a local
algebraic improvement. The native-window compiler and coefficient calibration
are not certified by these new Lean theorems, so this note does not claim an
end-to-end kernel-checked equivalence with Con(ZFC).

## Equation and coefficient convention

Use the complete coefficient tuple in
[`36-small-tuple/coefficients/COEFFICIENT_BINDING.json`](con-zfc-diophantine-forms/36-small-tuple/coefficients/COEFFICIENT_BINDING.json),
including its shifted `MF`. The four ports are `beta`, `K0`, `MC`, and `MF`;
`beta = B-1 > 0`. The unknowns retain the original order:

```
J, F, alpha, z, f, h, i, T, s, w, tau, eta, zeta, y, gamma.
```

Define polynomial abbreviations, without introducing additional unknowns:

```
q = beta*J+1,          C = q-F-alpha,
X = w*q,              Y = s*q^3,          E = X*Y,
k = eta+zeta,         c = k*Y+eta,        a = E+Y,
H = 4*a+3,            Delta = a^2+H,
D = X+a*c+gamma*H,
G = (q-1)*(q-F)+alpha,
R = G*(q^2-1)+(MC+q*MF)*J,
V = c*(T*f-1)-R*f^2.
```

The six factors are

```
N0 = tau^2-(X*Y^2)*(X*Y^2+1)*k^2,
N1 = D^2-Delta*c^2,
Na = Delta*(f^2-1)*(V^2-y^2)+y^2,
Nk = k-h*E-R,
Nt = (K0+w)*C+(q-F)-z*(q-1),
Ns = f^2-Delta*(i*c^2)^2.
```

The equation is

```
(N0-1)^2 + (Na-1)^2 + (Ns-1)^2 + (N1*Nk*Nt-1)^2 = 0.
```

## Why the zero set is preserved

At a zero of the unscaled product, all six factors are integer units. Four
factors must equal `+1`:

* `N0 != -1` follows from the elementary negative-Pell descent for
  `x^2-n*(n+1)*y^2`, with `n=X*Y^2 >= 2`.
* `N1 != -1` and `Ns != -1` follow from square residues modulo four, since
  `Delta=(a+2)^2-1`.
* Once `Ns=1`, its equation gives
  `Delta*(f^2-1)=(Delta*i*c^2)^2`. Substituting this square coefficient into
  `Na` excludes `Na=-1` modulo four.

The original product equation is therefore equivalent to the five equations
`N0=N1=Na=Ns=1` and `Nk*Nt=1`. These imply the four equations
`N0=Na=Ns=1` and `N1*Nk*Nt=1`. Conversely, multiplying these four equations
recovers the original product equation. Their sum of squared residuals vanishes
exactly when all four hold. The earlier local equivalence between the unscaled
product and P67 completes the proof.

[`ConsecutivePell.lean`](Lean/DiophantineConsistency/ConsecutivePell.lean)
checks the descent. [`ShortSystem.lean`](Lean/DiophantineConsistency/ShortSystem.lean)
checks the factor signs, four grouped equations, literal 75-gate evaluator, equality to
an ordinary `MvPolynomial (Fin 15) ℤ`, its degree bound `<= 68`, and its complete
positive-zero equivalence to P67. The relevant theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Operation count and exact degree

The P69 DAG has five final product/output gates. Delete those and the unused
`norm_pair` gate. A further operation is saved by sharing the already computed
`f^2-1`: compute the strong residual as

```
(f^2-1) - Delta*(i*c^2)^2
```

and delete the old `norm_strong` gate. This leaves 62 live producers. Two
multiplications form `N1*Nk*Nt`; four subtractions, four squarings, and three
additions complete the equation: `62+2+4+4+3 = 75`.

The earlier five-residual P77 remains available in
[`circuits/p77_sos.json`](circuits/p77_sos.json), with its literal Lean
certificate and audit. P75 has the same degree and costs two fewer operations.

The independent standard-library audit propagates valid degree envelopes and
top homogeneous forms through the literal gates, retaining valid envelopes
when a leading part cancels. Only the square of the strong residual reaches
degree 68. Even the direct degree envelope of the combined fourth residual is
at most 31, so its square has degree at most 62. The final leading homogeneous
form is

```
i^4*w^4*s^12*(eta+zeta)^8*(beta*J)^40.
```

In particular, the coefficient of `J^40*eta^8*i^4*w^4*s^12` is `beta^40`.
This proves the exact lower degree for the prescribed positive coefficient
tuple. The exact lower-degree assertion is supplied by the finite audit;
Lean separately checks the upper bound.

Reproduce the literal circuit and audit from the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_sos_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_sos_circuit.py
lake build DiophantineConsistency.ShortSystem
```

The deterministic ledger is
[`circuits/p75_sos.audit.json`](circuits/p75_sos.audit.json). No global
minimality or operation-count record is claimed.

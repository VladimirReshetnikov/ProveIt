# Exact Pell norms for the symbolic scalar candidate

The [symbolic-beta scalar construction](../trace74-symbolic-pell-projection-obstruction/README.md)
has two further ordinary-integer properties: the actual first `E` register
is a positive square, and its main ordinate has a positive square-root
witness for the corresponding Pell norm. These are identities for the
selected scalar candidate; **they do not show that its 74 graph value is
zero**, or solve the separate second square, auxiliary carrier, signed
main-index, or external-payload obligations.

For any even integer `z≥4`, define `y_0=0`, `y_1=1`,
`y_(j+1)=z*y_j−y_(j−1)`, and put

```text
x_j = y_(j+1) − (z/2)y_j.
```

The recurrence gives, by induction on `j`,

```text
y_(j+1)^2 − z*y_(j+1)*y_j + y_j^2 = 1,
x_j^2 − (z²−4)/4 * y_j^2 = 1.                     (1)
```

For `j>0`, `y_j>0` and `y_(j+1)≥(z−1)y_j` by induction, so `x_j>0`.
These are ordinary-integer statements; no model induction is asserted.

For the candidate put `P=XY²`, `k=2y_n(4P+2)`, and
`tau=x_n` at `z=4P+2`. Since `(z²−4)/4=4P(P+1)`, equation (1) yields

```text
tau² = 1+P(P+1)k²
     = 1+(XY)(kY)((XY)(kY)+k) = E.
```

This is exactly the natural register `E` defined in
[`Trace75Factors.lean`](../trace75-root-probe/Trace75Factors.lean), with
the same `X,Y,k`. Likewise, with `A=Y(X+1)` and `z=2(A+1)`, the
candidate's main ordinate `c=y_r(z)` satisfies, for a positive `x_r`,

```text
x_r² = 1 + A(A+2)c².
```

The candidate's `q|X`, `Y=q³`, positive `eta,zeta` and `k=eta+zeta`,
`c=kY+eta` allow a positive assignment to all ten coordinate *positions*,
for example `(1,F,C,1,1,X/q,1,1,eta,zeta)` with the selected positive
`F,C`. This merely supplies a valuation: it does not show that the
remaining graph factors vanish. Nor does the main Pell norm above supply
the separate graph requirement `1+delta*U²*E=f²`.

The checker exactly evaluates the analogous small construction
`B=7,n=63,r=77`, verifies both displayed norm identities and the actual
first `E` formula, and checks the scalar interval and selected residues.
It also checks the symbolic candidate's finite exponent identities, not
the enormous Pell values. It does not prove the recurrence induction,
evaluate the full graph, or verify object-theory derivability.

Run from the repository root:

```text
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-symbolic-pell-norms/check.py
```

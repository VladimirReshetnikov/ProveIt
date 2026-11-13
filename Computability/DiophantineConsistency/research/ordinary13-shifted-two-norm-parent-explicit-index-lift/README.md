# Explicit same-index sufficient condition for the parent lift

For a standard natural solution of the [shifted nine-variable two-norm graph](../ordinary9-shifted-free-aux-two-norm64/README.md)
with nonnegative ports and \(\beta>0\), let R be its literal rank and let
\(c=y_m(A)>0\) be its actual main Pell ordinate. If

\[
m\equiv3\pmod4,\qquad c\mid(R-m), \tag{†}
\]

then the original shifted 85-row parent has a natural zero preserving its
first/main coordinates. Both the strong witness and the auxiliary square
witness are given explicitly below. This is a **conditional** standard-integer
lift: neither part of (†) is proved for every two-norm zero, and no actual
zero, unconditional reverse bridge, model interpretation, Lean proof, or
iPRA/Con(ZFC) equivalence is claimed. The construction does not assume
\(m=R\).

This is a more restrictive but simpler corollary of the [general gcd/CRT lift](../ordinary13-shifted-two-norm-parent-crt-sufficient-condition/README.md):
it uses a fixed formula for the strong index, and sets the auxiliary index to
m directly, so no period search or CRT is needed in this special case.

## An explicit strong index

Let \(A=a+2\ge2\), \(\Delta=A^2-1\), and let \((x_j,v_j)\) be
the Pell sequence of multiplier A. Write \(x_m=g\), \(v_m=c\), and
let Q be its transition matrix. The Pell norm gives

\[
Q^{2m}=\mathrm{Id}+c
\begin{pmatrix}2\Delta c&2g\Delta\\2g&2\Delta c\end{pmatrix}.
\]

Set \(h=2mc\). Raising this identity to the cth power and expanding
binomially gives \(Q^h\equiv\mathrm{Id}\pmod{c^2}\), so
\(c^2\mid v_h\). Define

\[
f=x_h,\qquad i=\Delta v_h/c^2,\qquad I=c^2i=\Delta v_h.
\]

Because \(m,c,h>0\), f≥2 and i>0. The Pell norm gives
\(I^2=\Delta(f^2-1)\), so the literal parent strong factor is 1; also
\(f^2\equiv1\pmod c\), and \(\gcd(f,c)=1\). These witnesses are
specified by finite recurrences; their enormous numerical values need not be
expanded.

## Auxiliary index m and the actual rank

Let \((z_j,y_j)\) be the Pell sequence with multiplier I. The odd
quotient \(V=z_m/I\) is a positive integer. Write \(m=2j+1\); by
(†), j is odd. The odd-quotient polynomial identities in the general lift
show

\[
V\equiv-y_m(A)=-c\pmod{f^2},\qquad
V\equiv-m\pmod c.
\]

The first follows from \(I^2=\Delta(f^2-1)\); the second uses
\(I\equiv0\pmod c\). Together with \(c\mid(R-m)\) and
\(f^2\equiv1\pmod c\), the coprime moduli give
\(f^2c\mid V+c+f^2R\). Therefore

\[
T=\frac{V+c+f^2R}{f^2c}
\]

is an integer. R>0 follows from the actual first norm, beta>0, nonnegative
ports, and shifted positive F, alpha and k, as proved in the general lift;
thus T≥1. Set the parent's auxiliary input to \(y=y_m(I)\). Then
\(V=f^2(Tc-R)-c\), and the auxiliary Pell norm makes the parent
auxiliary factor 1. The untouched first and main residuals are zero, so the
literal parent output is zero. The shifted inputs \(i-1,T-1\) are natural.

The remaining scalar condition \(c\mid R-m\) is not deduced from the two
norms. Handling \(m\not\equiv3\pmod4\), proving the condition in the
actual models, or finding a different witness map remains open. The proof is
constructive in ordinary integers; formalizing its bounded iteration,
divisibility and Pell identities in a specific iPRA encoding is a separate
unperformed task.

## Reproduction

The checker pins and reproduces the general conditional packet, checks the
explicit period formula in bounded modular controls, and verifies the exact
fact-level toy \(A=2,m=3,c=15,h=90,R=18,T=2\). This toy has m≠R and
is not asserted to be a graph zero. The symbolic matrix and congruence
arguments above establish the general conditional statement; finite tests do
not. No Lean, build, staging, or giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-shifted-two-norm-parent-explicit-index-lift/check.py | cmp - research/ordinary13-shifted-two-norm-parent-explicit-index-lift/receipt.json
```

# Even main index obstructs the current strong-Pell auxiliary strategy

Let \(A\ge2\), \(\Delta=A^2-1\), and let \((x_j,y_j)\) be its
ordinary integer Pell sequence. Suppose the main ordinate is
\(c=y_m>0\) with **m even**. The strong-witness family used in the
[odd-index parent lifts](../ordinary13-shifted-two-norm-parent-odd-index-general-A/README.md)
chooses any h>0 with \(c^2\mid y_h\), then sets

\[
f=x_h,\qquad i=\Delta y_h/c^2,\qquad I=c^2i=\Delta y_h.
\]

For **every** such h, neither sign of any odd auxiliary Pell index can
satisfy the literal parent auxiliary factor-one equation at this same c and
f, for any integer R or T. Thus this particular strong-witness construction
cannot lift an even main index by choosing a different odd auxiliary index,
sign, or rank. It does **not** rule out another strong witness outside the
displayed family, a changed first/main valuation, or a parent zero; it does
not prove graph inequivalence or an iPRA theorem.

This obstruction is independent of compactness and applies to every integer
A≥2. In particular it applies to the actual fixed-compact graph whenever
its main index is even and the strong witnesses are chosen by this family.
It does not require \(m=R\).

## Why h is even

For any integer A, the Pell recurrence modulo 2 gives
\(y_j\equiv j\pmod2\): if A is even the coordinate pair alternates,
and if A is odd the x-coordinate is always 1 while y alternates. Thus m
even makes c even. Since \(c^2\mid y_h\), the ordinate \(y_h\) is
even and therefore h is even. The doubling formula gives
\(f=x_h=2x_{h/2}^2-1>1\), so f is odd and has an odd prime divisor p.
The Pell norm shows

\[
\Delta y_h^2\equiv-1\pmod p,
\]

so neither \(\Delta\) nor \(y_h\) is zero modulo p.

## No odd Pell ordinate can vanish modulo p

Let Q be the Pell transition matrix. Modulo p its hth power is the
invertible anti-diagonal matrix

\[
Q^h=\begin{pmatrix}0&\Delta y_h\\y_h&0\end{pmatrix}.
\]

Suppose an odd positive j had \(y_j\equiv0\pmod p\). Then the Pell
norm gives \(x_j=\pm1\pmod p\), so \(Q^j=\pm\mathrm{Id}\).
Because h is even, \((Q^j)^h=\mathrm{Id}\). But
\((Q^h)^j\) is invertible and anti-diagonal, so it cannot be the identity.
The two powers are equal, a contradiction. Negative odd indices are also
nonzero modulo p by \(y_{-j}=-y_j\).

For odd \(\ell\) and even m, both \(\ell-m\) and \(\ell+m\) are
odd. The Pell addition identity

\[
y_\ell^2-y_m^2=y_{\ell-m}y_{\ell+m}
\]

therefore shows \(y_\ell\not\equiv\pm c\pmod p\).

## Exact parent auxiliary implication

The actual shifted parent computes \(I=c^2i\),
\(Q_{\rm strong}=\Delta(f^2-1)=I^2\),
\(V=f^2(Tc-R)-c\), and its auxiliary factor
\(y^2-I^2(y^2-V^2)\). If that factor were 1, standard Pell
classification for \((IV)^2-(I^2-1)y^2=1\) would give an odd index
\(\ell=2j+1\) and a sign \(\epsilon\) with
\(V=\epsilon x_\ell(I)/I\). The quotient is integral and the graph's
V formula requires \(V\equiv-c\pmod{f^2}\).

As \(I^2=\Delta(f^2-1)\equiv1-A^2\pmod{f^2}\), the exact
odd-quotient polynomial identity used in the earlier lift gives

\[
\frac{x_{2j+1}(I)}I\equiv(-1)^j y_{2j+1}(A)\pmod{f^2}.
\]

The required V congruence would therefore make
\(y_\ell(A)\equiv\pm c\pmod p\), contradicting the previous section.
This uses both signs and does not use the value or parity of the graph's R.
At a candidate two-norm zero the first and main factors are already 1, and
this strong choice makes the strong factor 1, so the parent output cannot be
zero with these auxiliary choices.

## Reproduction

The checker pins the actual parent fields, earlier conditional lift and Pell
source. It verifies the source rows, tests the parity statement for even and
odd multipliers, checks bounded odd-prime/anti-diagonal controls and the
Pell addition identity (including negative indices), and provides a finite
fact-level example \(A=2,m=2,h=8,p=31\). The example is not claimed as
a full graph zero. The group and polynomial arguments above establish the
general obstruction; the finite tests do not. No Lean, build, staging,
model-provider replay, or giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-parent-even-main-strong-pell-obstruction/check.py | cmp - research/ordinary13-parent-even-main-strong-pell-obstruction/receipt.json
```

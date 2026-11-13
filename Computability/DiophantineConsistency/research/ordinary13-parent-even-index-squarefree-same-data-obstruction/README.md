# Squarefree discriminant: no same-data parent completion at an even index

Suppose standard natural first/main data satisfy the two actual norm equations
of the shifted two-norm graph, with main multiplier \(A\ge2\) and
\(c=y_m(A)>0\) at an **even** positive main index m. Put
\(\Delta=A^2-1\). If

\[
\Delta\text{ is squarefree},\qquad \gcd(m,\Delta)=1, \tag{†}
\]

then **no choice of the parent's auxiliary f, i, T, y inputs** completes
those same first/main data to a zero of the shifted 85-row parent. This is a
conditional same-data obstruction. It does not establish that such a
two-norm witness exists, that (†) holds at any fixed compact zero, that no
other first/main witness can work, or that the two equations differ in
existential zero status. No Lean, model, iPRA or Con(ZFC) theorem is claimed.

The conclusion strengthens the [previous even-index obstruction](../ordinary13-parent-even-main-strong-pell-obstruction/README.md):
under (†), **every** possible strong witness must belong to the previously
obstructed Pell family, rather than merely a particular chosen witness.

## An actual parent zero requires both auxiliary factors to be one

The parent's literal output is \(F_0F_1F_aF_s-1\). The assumed shared
first/main residuals make \(F_0=F_1=1\), so at a hypothetical parent
completion \(F_a,F_s\in\{1,-1\}\). The strong factor is

\[
F_s=1+I^2-\Delta(f^2-1),\qquad I=c^2i,\quad i\ge1.
\]

Since \(\Delta=a^2+4a+3\) is 0 or 3 modulo 4 and both I² and f²
are 0 or 1 modulo 4, \(F_s\) is never −1 modulo 4. Thus
\(F_s=F_a=1\), with the actual graph f and shifted positive i. In particular
\(I^2=\Delta(f^2-1)>0\) and \(f\ge2\). No assumption about the sign
of the first or main graph roots is needed here.

## Why every strong witness is in the obstructed family

The squarefree hypothesis and \(\Delta\mid I^2\) imply
\(\Delta\mid I\). Set \(v=I/\Delta>0\). Then
\(f^2-\Delta v^2=1\), so ordinary Pell classification with multiplier A
gives a positive h such that \(f=x_h(A)\) and \(v=y_h(A)\).

For the same main c, the exact relation

\[
\gcd(c,\Delta)=\gcd(m,\Delta) \tag{1}
\]

holds. To see it, let Q be the Pell transition matrix. Modulo \(\Delta\),
its off-diagonal part squares to zero, giving
\(y_m(A)\equiv mA^{m-1}\pmod\Delta\). Since
\(\gcd(A,\Delta)=1\), equation (1) follows. The second hypothesis in (†)
therefore makes \(\gcd(c,\Delta)=1\). From the actual graph identity
\(I=c^2i=\Delta v\) we obtain \(c^2\mid v=y_h(A)\).

Thus every strong witness in a hypothetical completion has exactly the form
excluded by the earlier even-index obstruction. That theorem applies to
**both signs** and every odd auxiliary Pell index, independently of the
actual rank R and T. Consequently the required \(F_a=1\) is impossible.

For even m, the coprimality hypothesis in (†) also forces \(\Delta\) odd;
in particular squarefreeness is a substantial extra condition and is not
asserted for the actual fixed graph. The argument neither uses nor assumes
\(m=R\).

## Reproduction

The checker pins and reproduces the preceding obstruction, verifies the
literal parent factor rows and all strong-factor mod-4 cases, and checks
bounded instances of (1) and the squarefree divisibility implication. A
small fact-level \(A=2,m=2\) strong witness is a control, not an actual
graph zero. The displayed standard-integer divisibility and Pell proof is
the general argument; bounded tests alone are not a proof. No Lean, build,
staging, model provider, or giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-parent-even-index-squarefree-same-data-obstruction/check.py | cmp - research/ordinary13-parent-even-index-squarefree-same-data-obstruction/receipt.json
```

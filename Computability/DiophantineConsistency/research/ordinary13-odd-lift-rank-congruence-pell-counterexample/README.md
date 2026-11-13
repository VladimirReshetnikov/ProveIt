# A Pell-level completion where the sufficient rank condition fails

The reviewed odd-index parent lift uses the sufficient condition
\(c\mid R+(-1)^{(m-1)/2}m\). The [correlated auxiliary congruences](../ordinary13-parent-strong-subgroup-rank-congruence/README.md)
do **not** force that scalar condition as an abstract Pell statement, even
with a fixed valid strong witness and an actual positive square-auxiliary
completion.

An exact counterexample is

\[
A=2,\quad \Delta=3,\quad m=3,\quad c=y_3(A)=15,\quad R=12,
\]

with the strong data and auxiliary index below. Since \(m\equiv3\pmod4\),
the sufficient scalar condition would require \(15\mid R-m=9\), which
is false.

This is a **fact-level** counterexample. R=12 is a rank placeholder, not a
rank extracted from a zero of the graph. In fact A=2 is impossible for the
actual shifted natural graph: its \(A=Y(X+1)+2\), with \(Y\ge1\)
and \(X\ge0\), is at least 3. Thus the example neither constructs a
two-norm or parent graph zero nor rules out the scalar condition for actual
graph zeros. It does not prove a model, Lean, iPRA or existential-equivalence
result.

## Fixed strong witness

Let \((x_j(A),y_j(A))\) be the Pell sequence of multiplier A. The main
pair is \((x_3,y_3)=(26,15)\). Take the **fixed** strong witness from
index 15:

\[
f=x_{15}(2)=189750626,\quad v=y_{15}(2)=109552575,\quad
I=3v=328657725,\quad i=I/15^2=1460701.
\]

These are positive integers and verify the actual strong equation
\(I=c^2i\), \(I^2=\Delta(f^2-1)\). Also
\(f^2\equiv1\pmod c\), consistent with the reviewed strong-subgroup
necessary condition. No inference about other strong witnesses is needed.

## Correlated congruences and a positive auxiliary completion

Set the odd auxiliary index and sign to

\[
\ell=218943027,\qquad \sigma=-1.
\]

It satisfies \(\ell\equiv3\pmod4\), \(\ell\equiv12=R\pmod{15}\),
and the exact modular Pell computation gives

\[
y_\ell(2)\equiv15\pmod{f^2}.
\]

Thus both correlated conditions hold **with the same sign**:
\(y_\ell(A)\equiv-\sigma c\pmod{f^2}\) and
\(\ell\equiv-\sigma R\pmod c\).

Let \((z_j,y_j)\) be the Pell sequence of multiplier I, and define the
positive integer \(W=z_\ell/I\). The quotient is integral because
\(\ell\) is odd. Its value is enormous and is **not expanded**. The
checker instead evaluates its exact integer quotient polynomial modulo
\(f^2c\), obtaining

\[
W\equiv-15\pmod{f^2},\qquad W\equiv3\pmod{15}.
\]

It follows that
\(T=(W+15+12f^2)/(15f^2)\) is a positive integer. Taking
\(V=W\), \(y=y_\ell(I)\) gives the literal auxiliary relation
\(V=f^2(Tc-R)-c\), and its Pell norm gives
\(y^2-I^2(y^2-V^2)=1\). Therefore the fixed strong equation and the
square auxiliary factor are both actually satisfied at this fact-level
rank, despite the failure of the scalar condition.

## Reproduction

The checker pins the original parent field rows and the reviewed correlated
congruence source, computes the small main/strong pairs exactly, and checks
\(I=c^2i\). It verifies \(y_\ell(A)\) modulo f² by binary Pell
powering. For W it uses the **integer-polynomial recurrence**
\(P_{j+2}=(4I^2-2)P_{j+1}-P_j\), \(P_0=1\),
\(P_1=4I^2-3\), modulo \(f^2c\); it never divides by a modular
nonunit. Only about 28 binary exponentiation steps are needed. The selected
index can be checked against its recorded small CRT residues; the modular
checks themselves supply the exact certificate. No enormous Pell coordinate,
Lean process, build, staging or model provider is used.

```sh
python3 -I -S -B research/ordinary13-odd-lift-rank-congruence-pell-counterexample/check.py | cmp - research/ordinary13-odd-lift-rank-congruence-pell-counterexample/receipt.json
```

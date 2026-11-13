# Modular obstructions to two fixed-port power-match families

At the exact compact ports, write \(\beta=2^{67\cdot8807}-1\),
\(q=1+\beta J\), and let \(MC,MF\) be the pinned low and shifted-high
mask constants. The graph computes

\[
R=G(q^2-1)+J(MC+qMF).
\]
Two power-matching choices for the Pell indices are blocked as follows.

* For **every** natural \(J\) for which \(q\) is a power of 2, the exact
  matching \(n=L(2L+1)\), \(R=2n-1\) is impossible.
* For \(J=1\), the exact matching \(n=L(L-1)\), \(R=2n-1\) is impossible.

These are constraints on particular proposed witnesses, not a proof that the
fixed-port i-unshift graph lacks a zero. The second conclusion is not claimed
for other J; both leave shifted rank relations and other witness maps open.

## Shared compact recipes and the first family

Modulo 3, the source-defined values are \(\beta\equiv MC\equiv MF\equiv1\).
If \(q\) is a power of two, \(q\equiv\pm1\) and \(q^2-1\equiv0\).
Because \(q=1+\beta J\), also \(J\equiv q-1\). Thus the actual rank obeys

\[
R\equiv J(1+q)\equiv q^2-1\equiv0\pmod3.
\]
In contrast \(2L(2L+1)-1\) is 2, 2, 1 modulo 3 when L is 0, 1, 2.
This proof deliberately does not assert the conclusion when 3 divides q.

## The second family: an independent prime obstruction

Let \(p=193707721\). Exact trial division through \(\lfloor\sqrt p\rfloor\)
shows it is prime; modular exponentiation shows \(2^{67}\equiv1\pmod p\).
Consequently \(\beta\equiv0\), \(q\equiv1\), and the finite mask digit
recipes give

\[
 MC\equiv193706734,\quad \mathrm{highNat}\equiv55802646,\quad
 MF=\beta+\mathrm{highNat}\equiv55802646\pmod p.
\]
With \(J=1\), the actual rank therefore satisfies
\(R\equiv55801659\pmod p\). If \(R=2L(L-1)-1\), completing the square
requires

\[
 (4L-2)^2\equiv8R+12\equiv58997842\pmod p.
\]
Euler's criterion gives \(58997842^{(p-1)/2}\equiv p-1\), a non-square.
Therefore no integer L can satisfy this required congruence. For general J
one has \(R\equiv J(MC+MF)\pmod p\), so the J=1 non-square calculation
alone does not rule out other J.

## Why the alternate offset was worth checking

Take \(Y=2^L\), \(X=2^m\), \(m=n+d\), \(P=2XY\), and \(Q=4XY^2\).
The leading powers satisfy \(P^{m-1}=2YQ^{n-1}\) exactly when

\[
 n(L+1-d)=d(d+L+1).
\]
For \(d=L-1\), this gives \(n=L(L-1)\) and \(m=L^2-1\). The previous
modulo-3 calculation alone does not exclude this offset: for \(L\equiv2\)
its matched rank \(2L(L-1)-1\) is 0 modulo 3.

The alternative offset is also compatible with the *Pell ordinate interval*
needed for \(0<\eta=c-Yk<k\). With the same recurrence and definitions
\(k=2y_n(2XY^2+1)\), \(c=y_m(Y(X+1)+2)\) as the pinned coarse-bounds
construction, the elementary bounds on ordinates in that construction give
\(c>Yk\), since \(m>n\), the matched leading powers are equal, and the
main lower-bound relative increment exceeds the first upper-bound relative
increment. The reverse bounds give

\[
\frac c{Yk}\le(1+2/X)^{m-1}<1+1/Y
\]
whenever \(4(m-1)Y<X\). For \(L\ge4\), that last inequality is
\(4(L^2-2)<2^{L^2-L-1}\), true at 4 and thereafter by induction.
Thus the interval itself does not contradict this offset. In the fixed-port
setting \(L\ge3(67\cdot8807)\) also makes \(Y/q^3\) natural for J=1.
These statements establish neither the actual graph rank equality nor the
remaining factor and divisibility conditions; the prime obstruction shows the
required rank equality cannot hold in this J=1 family.

## Reproduction and limits

From `Computability/DiophantineConsistency`, run

```sh
python3 -I -S -B research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/check.py | cmp - research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/receipt.json
```

The checker pins the literal graph and the exact beta, low-digit and high-digit
recipes, evaluates the high digits independently using Horner and a weighted
sum, performs complete trial division and Euler's criterion, and checks small
controls for the power identity and inequality. The displayed algebra and
induction are the general argument; finite controls are not a general proof.
No huge coefficient or Pell ordinate is expanded. This is standard-integer
source-level evidence, not a Lean, iPRA or all-model proof.

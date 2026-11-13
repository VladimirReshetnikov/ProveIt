# Necessary congruences for F = 0, C > 0 at the compact ports

Consider the literal [F-unshift probe](../ordinary13-eta85-shift-boundary-probes/F-probe.json)
at the exact compact ports, in ordinary integers, in the restricted slice
\(J=1\), \(F=0\), \(C=q-\alpha>0\). Suppose **the first and main residuals
both vanish**. Put

\[
q=\beta+1=2^{67\cdot8807},\quad X=qw,\quad Y=q^3s,\quad
U=q^2Y,\quad M=XY^2,\quad k=\eta+n_\zeta+1.
\]
The graph enforces \(s\ge1\) and \(\alpha\ge1\). The norms and their
actual signed roots then have all the following necessary consequences:

* \(X>0\), \(k>q\), \(1\le C\le q-1\), and **C is odd**.
* \(\beta\mid C(w+K_0)\).
* With the literal rank
  \(R=(q^2-C)(q^2-1)+MC+qMF\), one has
  \(k\equiv R+1\pmod{q^5}\).
* There is a natural first-Pell index \(n\ge2\) with
  \(k\equiv2n\pmod{4M}\), and consequently
  \(2n\equiv R+1\pmod{q^5}\).

These constraints do **not** exclude the branch, construct a zero, prove a
zero-preserving map, or imply the user's iPRA endpoint. The full graph being
zero does not by itself appear among the hypotheses: extraction of the two
residual equations from a product zero is a separate factor-unit argument.
The compact-port case with other values of J remains open. The proof below is
standard-integer arithmetic; the referenced Lean sources are not executed or
claimed to provide an elaborated proof of this packet.

## Signed first root and X positivity

For F=0 the first carrier is \(B=C(X+K_0)\), and the literal signed root is
\(Z=\beta(\ell+k+r-kB)-B\), \(\ell=Mk\). Its vanishing residual gives
\(Z^2=\beta^2(1+M(M+1)k^2)\), hence \(\beta\mid Z\) and
\(\beta\mid B\). Since \(q\equiv1\pmod\beta\), this implies the stated
\(\beta\mid C(w+K_0)\). The root may be negative; only its square and
integer divisibility are used.

The main root is
\(D_*=U(X+ac)+H(U\gamma+R+1-k)\), with
\(a=Y(X+1)\), \(H=4a+3\), and \(\Delta=a^2+H\). Its vanishing
residual gives \(D_*^2=U^2(1+\Delta c^2)\). Thus \(D_*=Ud\) for a
signed integer d, and \(d^2-\Delta c^2=1\).

If \(X=0\), then \(a=Y\), \(H=4Y+3\), and the root equation yields
\(H\mid U(d-ac)\). Because
\((d-ac)(d+ac)=1+Hc^2\), the factor \(d-ac\) is invertible modulo H;
therefore \(H\mid U=q^2Y\). It follows that \(H\mid3q^2\), since
\(4q^2Y=q^2(H-3)\). But \(H\ge4q^3+3>3q^2\), a contradiction.
This is the same fact-level route as the cited eta-natural X-positivity source;
it uses neither sign of the rank nor positivity of eta.

The separate [main-ordinate argument](../ordinary13-eta85-main-ordinate-q-bound/README.md)
gives \(k>q\) under the same main norm, independently of F and C.

## First Pell index, rank and parity

Because \(M>0\), the natural integer \(x=|Z|/\beta\) satisfies
\(x^2-M(M+1)k^2=1\). First-Pell descent using the unit
\((2M+1,2)\) gives an index n and

\[
(x,k)=\operatorname{Pell}_{M(M+1)}(2M+1,2)^n.
\]
For reference, the pinned `ArithmeticPellFirstNorm` source states this
classification and evenness for positive parameter M. The descent is also
an elementary integer argument: k=1 lies between consecutive squares;
for k≥2 the inverse unit gives a nonnegative smaller ordinate, so induction
reaches (1,0). In the recurrence, \(x\equiv1\pmod{2M}\) and k is even,
so each step increases k by 2 modulo \(4M\). Therefore
\(k\equiv2n\pmod{4M}\). Since \(k>q\ge2\), \(n\ge2\).

Because q is a power of 2 and \(Y=q^3s\), the modulus H is odd and
\(U=q^5s\). From the actual signed-root equation,
\(q^5\mid H(R+1-k)\), and oddness of H permits cancellation:
\(k\equiv R+1\pmod{q^5}\). As \(M=XY^2=q^7ws^2\), also
\(q^5\mid4M\), giving the first-index congruence.

For F=0, \(G=\alpha+q(q-1)=q^2-C\), so the graph's rank has the form
stated above, and \(R\equiv C+MC\pmod q\). The compact low-mask digit at
index zero is \(2^{67}-2\): zero belongs to the pinned support and is not
its exceptional slot. All higher digits are even multiples of the base;
therefore MC is even. Since \(k\) is even and q is even, the congruence
\(k\equiv C+MC+1\pmod q\) forces C odd.

## Reproduction

The checker pins the literal graph, concrete coefficient and first-norm
sources, and the predecessor gap arguments. It verifies the relevant graph
rows, compact low-digit parity, and bounded recurrence and congruence
controls. Those controls are not the universal proof above. No large compact
numeral, Lean process, build or model provider is used.

```sh
python3 -I -S -B research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences/check.py | cmp - research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences/receipt.json
```

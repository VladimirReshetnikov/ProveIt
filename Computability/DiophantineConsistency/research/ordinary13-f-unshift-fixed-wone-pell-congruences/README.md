# Fixed F-unshift slice: w=1 Pell-index and sign constraints

For an ordinary natural full zero of the literal F-unshift graph at the exact
compact tuple, restrict to \(F=0\), \(J=1\), \(C=q-\alpha>0\),
and **w=1**. Set

\[
N=67\cdot8807=590069,\quad q=2^N,\quad
Y=q^3s,\quad a=Y(q+1),\quad H=4a+3,\quad g=\gcd(s,3).
\]

The existing source-pinned norm and gcd packets imply \(C=q-1\),
\(\alpha=1\), and a positive first-Pell index n satisfying

\[
n\equiv-1\pmod{2^{66}},\qquad n\ge2^{66}-1.
\]
The actual signed main root has a main-Pell index \(m\ge1\). If that root
is positive, then \(2^m\equiv q\pmod{H/g}\); if it is negative, then
\(-2^{-m}\equiv q\pmod{H/g}\). The inverse exists because H/g is odd.
If \(3\nmid s\), these respectively force **m odd and eta odd**, or
**m even and eta even**. In the negative-root branch the strong and auxiliary
unit equations further force f and y odd, with y≥3.

These are necessary conditions for this exact full-zero slice; they do not
prove a contradiction, construct a witness, or decide the odd-index auxiliary
Pell condition. Other w, F, J, and model interpretations remain open. No Lean,
build, or iPRA result is claimed.

## First-Pell index

The [fixed-kernel gcd calculation](../ordinary13-f-unshift-fixed-small-power-w-gcd/README.md)
gives \(\gcd(\beta,K'+1)=1\); together with the actual first residual it
forces \(C=\beta=q-1\) and \(\alpha=1\). The
[unit-factor and norm analyses](../ordinary13-f-unshift-fixed-strong-aux-necessary-condition/README.md)
then yield

\[
2n\equiv R+1\pmod{q^5},\qquad
R=(q^2-C)(q^2-1)+MC+qMF.
\]
The pinned fixed low-mask digit zero is \(2^{67}-2\), so
\(MC\equiv-2\pmod{2^{67}}\). Since \(2^{67}\mid q\) and
\(C=q-1\), reduction of the actual rank gives
\(R+1\equiv C+MC+1\equiv-2\pmod{2^{67}}\). Therefore
\(n\equiv-1\pmod{2^{66}}\), proving the stated lower bound.

## Main-Pell sign and actual root

Let \(U=q^5s\), \(c=Yk+\eta>0\), and let \(D_*=Ud\) be the actual
signed graph root after extracting the main norm. With \(A=a+2\), its norm
is \(d^2-(A^2-1)c^2=1\), so Pell descent yields a unique positive index
m with \((|d|,c)=(x_m,y_m)\), where the recurrence has multiplier A.
The literal root is

\[
D_*=U(q+ac)+H(U\gamma+R+1-k).
\]

Because H is odd and \(H\equiv3\pmod s\),
\(\gcd(H,U)=\gcd(H,s)=\gcd(s,3)=g\). Therefore the root equation
requires \(d-ac\equiv q\pmod{H/g}\).

The main Pell recurrence gives
\(x_m-ay_m\equiv2^m\pmod H\): the difference at each step from twice
the preceding one is exactly \(Hy_m\). Moreover
\((x_m-ay_m)(x_m+ay_m)=1+Hy_m^2\), so
\(x_m+ay_m\equiv2^{-m}\pmod H\). The two possible signs of d now yield
exactly the two necessary congruences stated above. They are necessary root
conditions; satisfying either does not establish the remaining quotient,
nonnegative gamma, first/strong/auxiliary factors, or a full zero.

For \(3\nmid s\), g=1, while \(3\mid H\) because \(q+1\) is a
multiple of 3. As N is odd, \(q\equiv-1\pmod3\). Reducing the positive
root congruence modulo 3 forces m odd; reducing the negative root congruence
forces m even. The multiplier A is even, so \(y_m\equiv m\pmod2\).
Since \(c=Yk+\eta=y_m\) and Y is even, eta has the same parity as m.

In the negative-root branch, c is even, hence \(I=c^2i\) is even. The
pinned unit-factor extraction gives \(\Delta(f^2-1)=I^2\) and
\(y^2-I^2(y^2-V^2)=1\). Reduction modulo 8 forces f odd; reduction modulo
4 forces y odd. The separately established inequality y≥2 makes y≥3.
The auxiliary index still must satisfy the explicit conditional divisibility
and positive-T criterion in the preceding packet; its solvability is unknown.

## Reproduction

The checker pins the literal graph, compact low digit, earlier gcd and norm
packets, and Pell source. It checks the exponent and residue calculations,
verifies the signed Pell congruences and gcd in bounded controls, and includes
a noncompact \(q=2\), \(H=99\) control for both signs. The general
algebra above is the proof; finite controls do not establish a graph zero.
No huge constant or Pell ordinate is expanded.

```sh
python3 -I -S -B research/ordinary13-f-unshift-fixed-wone-pell-congruences/check.py | cmp - research/ordinary13-f-unshift-fixed-wone-pell-congruences/receipt.json
```

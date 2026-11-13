# Fixed F-unshift slice: factor units and the remaining auxiliary condition

For the literal [F-unshift graph](../ordinary13-eta85-shift-boundary-probes/F-probe.json)
at the exact compact ports, consider a standard natural-number full zero with
\(J=1\), \(F=0\), and \(C=q-\alpha>0\). Then all four graph factors are
\(+1\). In particular the first and main residuals vanish, so every necessary
congruence in the [preceding packet](../ordinary13-f-unshift-fixed-positive-gap-norm-congruences/README.md)
applies to the same valuation. The actual strong and auxiliary fields satisfy

\[
\Delta(f^2-1)=I^2,\qquad
(I^2-1)y^2-I^2V^2=-1,\quad
I=c^2i,\quad V=f^2(Tc-R)-c.
\]

This packet further gives an exact remaining auxiliary Pell-index condition
for any chosen strong solution. It neither constructs a full graph zero nor
rules one out, and does not prove a reverse witness map, Lean theorem, model
transfer or iPRA endpoint. All statements here concern standard integers.

## Exact full-output factor extraction

The pinned literal output is \(F_0F_1F_aF_s-1\), with
\(F_0=1+A_0\), \(F_1=1+A_1\), \(F_s=1+I^2-Q\),
\(Q=\Delta(f^2-1)\), and
\(F_a=y^2-Q(y^2-V^2)\). If the output is 0, these four integer factors
are individually \(\pm1\).

In this slice \(q=2^{67\cdot8807}\), \(Y=q^3s\),
\(a=Y(X+1)\), and \(\Delta=a^2+4a+3\equiv3\pmod8\).
Squares modulo 8 are 0, 1, 4. For \(f^2\equiv0,1,4\), respectively,
\(Q\equiv5,0,1\pmod8\). None of the possible residues
\(1+I^2-Q\) is \(-1\pmod8\), so \(F_s=1\). More precisely, a
strong +1 unit requires either f odd and \(4\mid I\), or
\(f\equiv2\pmod4\) and I odd.

The main residual has form \(D_*^2-U^2(1+\Delta c^2)\), with
\(U=q^5s\). Since \(4\mid U^2\), its factor satisfies
\(F_1\equiv1+D_*^2\pmod4\), which is 1 or 2, never \(-1\).
Consequently \(F_1=1\); no divisibility of the root is assumed.

For the first factor, its literal residual is
\(A_0=Z^2-\beta^2(1+\ell(\ell+k))\), where
\(\ell=XY^2k\) is divisible by 4 and \(\beta=q-1\) is odd. Thus
\(F_0\equiv Z^2\pmod4\), excluding \(-1\), and \(F_0=1\).
The product being 1 then forces \(F_a=1\). These calculations respect the
actual graph's shifted \(\zeta=n_\zeta+1\), so
\(k=\eta+n_\zeta+1\ge1\); no eta-positive assumption is used.

## The strong field and y ≥ 2

Here \(i=n_i+1\ge1\), \(c=Yk+\eta\ge Y\ge8\), and
\(I=c^2i\ge64\). The strong equation makes \(f\ge2\). Applying the
preceding packet's first-Pell classification to the already extracted first
and main norms gives \(X>0\), a first index \(n\ge2\), and, by increasing
first-Pell ordinates,

\[
k\ge8M+4,\qquad M=XY^2.
\]
It follows that \(c\ge Yk>Y(X+1)+2=a+2\), so
\(\Delta=(a+2)^2-1<c^2\). The strong equation therefore implies

\[
f^2-1=\frac{c^4i^2}{\Delta}>c^2\ge c,
\quad\text{hence}\quad f^2>c+1.
\]
This inequality uses the first-norm growth; the strong equation alone does not
justify it.

The auxiliary equation rules out y=0 because \(I>1\). If y=1, it gives
\(V=\pm1\). But \(V\equiv-c\pmod{f^2}\), and
\(1<c<f^2-1\), so neither signed value is possible. Thus \(y\ge2\).

The strong equation alone is not an obstruction: for any positive c and
\(\Delta=(a+2)^2-1\), the Pell recurrence of multiplier \(a+2\) has a
positive index j with ordinate \(v_j\equiv0\pmod{c^2}\), since its
transition matrix is invertible modulo \(c^2\). Setting
\(f=u_j\), \(i=\Delta v_j/c^2\) gives
\(\Delta(f^2-1)=(c^2i)^2\), with f and i positive. This construction does
not enforce any main, rank or auxiliary condition.

## Exact remaining auxiliary condition

Fix positive graph data \(c,\Delta,f,i,R\) satisfying the displayed strong
equation and the norm-derived inequalities. Write \(I=c^2i\), and let
\((x_m,y_m)\) be the Pell sequence with multiplier I:

\[
(x_0,y_0)=(1,0),\qquad
(x_{m+1},y_{m+1})=(Ix_m+(I^2-1)y_m,\ x_m+Iy_m).
\]
For this chosen strong solution, existence of natural y and graph coordinate
\(T\ge1\) satisfying the auxiliary factor is equivalent to existence of an
**odd m ≥ 3** and \(\epsilon\in\{-1,1\}\) such that

\[
\frac{\epsilon x_m/I+c+f^2R}{f^2c}
\quad\text{is an integer at least 1}. \tag{*}
\]

Indeed, the auxiliary equation is the Pell norm
\((IV)^2-(I^2-1)y^2=1\). Integer Pell descent with fundamental unit
\((I,1)\) gives \((I|V|,y)=(x_m,y_m)\); modulo I, x_m is divisible
by I exactly when m is odd, since the recurrence alternates between 0 and
\(\pm1\). The excluded m=1 case is precisely y=1. Conversely any odd m≥3
and sign satisfying (*) determines \(V=\epsilon x_m/I\),
the indicated positive T, and \(y=y_m\), which satisfy the literal auxiliary
factor. This is an exact conditional reformulation, not a claim that (*) is
solvable for the actual rank and first/main witnesses.

## Reproduction

The checker replays the pinned norm-congruence packet, verifies the actual
shifted-zeta, unit-product and strong/auxiliary graph rows, exhausts the
strong-factor residues modulo 8, and runs bounded strong and auxiliary Pell
controls. The general arguments above, not those finite controls, justify the
claims. No Lean or build is run.

```sh
python3 -I -S -B research/ordinary13-f-unshift-fixed-strong-aux-necessary-condition/check.py | cmp - research/ordinary13-f-unshift-fixed-strong-aux-necessary-condition/receipt.json
```

# Independent review: first/main index boundary

The corrected [source packet](../../research/ordinary13-free-aux-square-first-main-index-boundary/README.md)
correctly excludes a standard-integer zero of the free auxiliary-square graph
in the exact compact slice \(J=1,w=1,s=1\) whenever its main ordinate is
represented by a **positive** index \(m\le q^2\). It leaves \(m=0\),
all larger indices, and other slices open. No global zero-existence or Lean
result follows.

The literal natural graph has \(k=\eta+\zeta\), with no extra 1, and
\(c=\eta+q^3k\). If a supplied m is positive, its Pell ordinate c is
positive. Thus k=0 would force \(\eta=\zeta=c=0\), a contradiction;
only then may the proof use k>0. A graph zero with c=0 is outside this claim.

At a product zero each integer factor is ±1. Here \(q=2^{590069}\),
\(\beta=q-1\), \(U=q^5\), and \(\ell=q^7k\). The first factor
\(1+Z^2-\beta^2(1+\ell(\ell+k))\) is \(Z^2\) modulo 4 and cannot be
−1. The main factor is \(1+D_*^2\) modulo 4 and also cannot be −1.
Thus both actual residuals are zero; the signed roots need not be positive.

With the graph's positive F and alpha, put \(C=q-F-\alpha\) and
\(B=C(q+K_0)-F\). If C≤0, then B<0 and the literal first root
\(Z=\beta(\ell+k+r-kB)-B\) is strictly greater than
\(\beta(\ell+k)\). Its required square is at most the square of that
bound because \(\ell k+k^2-1\ge0\), a contradiction. Hence C>0,
so \(F+\alpha<q\), and the actual rank coefficient
\(G=\alpha+(q-F)(q-1)\) obeys \(2q-1\le G<q^2\).

The fixed digit recipes give \(0\le MC<q\) and \(0\le MF<2q\):
the low mask has digits below \(2^{67}\) and a strict deficit at index 0;
the high-mask list has length 8807 and top digit zero, so its value is below
\(\rho^{8806}<\beta\), while \(MF=\beta+\mathrm{highNat}\).
Consequently the literal rank \(R=G(q^2-1)+MC+qMF\) satisfies
\(2q^2<R+1<q^5\) for q≥8.

The first norm has parameter \(M=q^7\). First-Pell descent gives n≥1,
\(k=2y_n(2M+1)\), and \(k\equiv2n\pmod{4M}\). The actual signed
main-root equation and odd \(H=4a+3\) give
\(k\equiv R+1\pmod{q^5}\). Thus \(2n\equiv R+1\pmod{q^5}\).

The index comparison checks: if n>m, the standard Pell ordinate bounds give
\(c\ge q^3k\ge2q^{7(n-1)+3}\ge2q^{7m+3}\), whereas
\(c=y_m(q^3(q+1)+2)\le q^{5(m-1)}\), since twice its multiplier is
strictly less than \(q^5\). These inequalities are incompatible, so n≤m.
For positive \(m\le q^2\), this yields
\(0<2n\le2q^2<R+1<q^5\), impossible under the displayed congruence.

The independent checker pins the corrected author packet, literal graph,
fixed mask sources and first-Pell source; it checks the exact no-extra-one k
wiring, unit-factor residues, rank bounds over bounded controls, and bounded
Pell comparisons. Those finite controls do not replace the general argument
above. The author receipt reproduces. No Lean, build, staging, model-provider
validation, or proof of an internal arithmetic endpoint was performed.

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-first-main-index-boundary-independent/check.py | cmp - reviews/ordinary13-free-aux-square-first-main-index-boundary-independent/receipt.json
```

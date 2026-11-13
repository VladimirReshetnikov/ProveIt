# Independent review: positive-J carrier60 counterexample

The [reviewed witness](../../research/ordinary10-carrier60-positive-j-mask-bounds-counterexample/README.md)
is an exact natural zero of the 60-operation carrier graph with \(J=1\),
\(\beta=1\), \(MC=0\), \(MF=1\), and any natural \(K_0\). Hence it
also works for every positive K0 and satisfies the stated coarse port bounds
\(\beta>0\), \(MC<\beta\), and \(MF<2\beta\). Its reconstructed
old coordinate \(\alpha=q-F-C\) is −8, so the direct inverse to the
61-operation graph cannot use this same valuation.

The conclusion does not apply the actual compact beta, and it does not prove
that the 60- and 61-operation equations differ in existential zero status:
a different witness map could exist. It is a standard-integer coordinate
inverse obstruction, not a Lean/model, parent-equivalence, iPRA or Con(ZFC)
result.

For \(J=1,F=1,C=9,w=s=1\), the literal fields are
\(q=2\), \(X=2\), \(Y=8\), \(U=32\), \(a=24\),
\(H=99\), and \(\Delta=675\). The actual rank is
\((q(q-F)-C)(q^2-1)+J(MC+qMF)=-19\). For every K0,
\(h=9K_0+17\) makes the exact carrier residual
\(C(X+K_0)-F-\beta Jh\) zero. The inferred alpha is
\(q-F-C=2-1-9=-8\).

The checker independently computes the two displayed Pell pairs by binary
powering, rather than the author's step-by-step iteration. It verifies both
norms, \(8k\le c<9k\), the required signed main-root divisibility,
and natural eta, shifted-zeta and gamma. Their first and main ordinate sizes
are respectively 7,692 and 7,695 bits; the exact values are not printed.
It then evaluates **all 60 literal graph rows** over the polynomial ring
\(\mathbb Z[K_0]\), obtaining the documented actual rank and main root,
three zero residuals and zero output identically in K0. This proves the
arbitrary-K0 claim rather than testing selected K0 values.

Replacing the graph's J input with a shifted positive J would still admit
this witness at its new input 0. That observation addresses the displayed
coordinate inverse under the coarse bounds, not the fixed-compact tuple or
all possible inverse maps. The author receipt and independent review receipt
reproduce. No Lean, build, staging or provider validation was performed.

```sh
python3 -I -S -B reviews/ordinary10-carrier60-positive-j-mask-bounds-counterexample-independent/check.py | cmp - reviews/ordinary10-carrier60-positive-j-mask-bounds-counterexample-independent/receipt.json
```

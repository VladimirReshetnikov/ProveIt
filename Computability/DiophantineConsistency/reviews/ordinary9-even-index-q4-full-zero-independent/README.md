# Independent review: noncompact q=4 even-index zero

The [reviewed packet](../../research/ordinary9-even-index-q4-full-zero/README.md)
correctly gives an exact natural zero of both the literal 9/64 and 10/61
two-norm graphs at ports \((3,1,1,1)\), with main Pell index 84. The
[reviewed even-index theorem](../ordinary13-parent-even-index-unconditional-independent/README.md)
therefore rules out choosing auxiliary inputs that complete these **same
first/main data** to a shifted-parent zero. This does not exclude different
parent data at those ports, establish existential inequivalence, or address
the fixed compact tuple.

The independent checker reconstructs the two Pell pairs using binary
exponentiation, rather than the author's step-by-step iteration. With
\(q=4\), \(X=2^{84}\), \(Y=64\), \(U=1024\),
\(M=XY^2\), \(a=Y(X+1)\), and \(H=4a+3\), it checks

\[
\tau^2=1+M(M+1)k^2,\quad
g^2=1+((a+2)^2-1)c^2,\quad 64k\le c<65k.
\]

It separately verifies the exact divisions \(3\mid B\),
\(H\mid g-X-ac\), \(U\mid k-R-1\), and \(q\mid X\), and checks
that h, r, eta, shifted zeta and gamma are all natural. The actual rank is
155. It evaluates all 64 and all 61 graph rows with the reconstructed
inputs: both outputs vanish; the nine-variable first root is \(Z=3\tau\),
the ten-variable carrier and normalized first residual vanish, and both
actual main roots are \(D_*=Ug\). The largest input has 7,644 bits and no
large decimal witness is printed.

A separate exact expression-tree comparison confirms that the nine-variable
first/main residuals, rank, c and signed main root are the same fields of the
shifted parent at the shared coordinates. The supplied main ordinate is
literally \(y_{84}(a+2)\); 84 is positive and even. Thus the reviewed
theorem applies to precisely these data, while allowing any alternative
first/main data to remain open.

The author's receipt and this receipt reproduce under the documented bounded
process limits. No Lean, build, staging, model-provider
or iPRA validation was performed.

```sh
timeout 15s python3 -I -S -B reviews/ordinary9-even-index-q4-full-zero-independent/check.py | cmp - reviews/ordinary9-even-index-q4-full-zero-independent/receipt.json
```

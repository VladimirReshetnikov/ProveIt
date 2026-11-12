# Independent source review: eta-natural first/main norm and large k

The fact-level proposal preserves positive X, Y and zeta and assumes both the explicit natural first and main norms. It allows eta=0. Since `k=eta+zeta>0` and `M=X*Y²>0`, the pinned `ArithmeticPellFirstNorm.two_le_ordinate` source excludes k=1 after identifying the discriminant using the justified predecessor `M-1`.

At k=2, positive zeta gives `eta<=1`; consequently `c=eta+2Y` lies strictly between 1 and `2A`, where `A=XY+Y+2`. The pinned generic `no_main_square` source then excludes the displayed main norm, because its right-hand side would lie strictly between `(A*c-1)²` and `(A*c)²`. This includes eta=0, zeta=2 as well as eta=zeta=1; it does not invoke the older bundled lemma that assumes eta>0. Thus k>2, and the separately proposed `first_ordinate_large` applies to obtain `k>=8M+4` under the first norm.

`MainSquareGap` and `AuxRootBounds` are unelaborated research-source providers and have their own transitive dependencies. The client assumes, rather than extracts, both natural roots, graph factor units, the two norms and all positivity/port conditions. Its finite receipt reproduces, and independent controls exercise the square-gap inequalities; no Lean elaboration, eta-unshifted graph zero map, provider replay or iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-natural-norm-large-k-independent/check.py | cmp - reviews/ordinary13-eta-natural-norm-large-k-independent/result.json
python3 -I -S -B research/ordinary13-eta-natural-norm-large-k-draft/check.py | cmp - research/ordinary13-eta-natural-norm-large-k-draft/result.json
```

# Independent review: shifted-Pell positive-input graph

The [candidate](../../research/ordinary14-shifted-pell75/README.md) is sound
as an external reduction conditional on the reviewed positive-74 parent's
unit-factor argument and inherited endpoint. It gives 14 strictly positive
inputs, an explicit 75-operation graph and exact degree 97 at the externally
authenticated P72/P115 ports. The operation count is an upper bound, not a
minimality result.

The parent first factor is `r²−ell*(ell+k)`, and `r` occurs only in its
replaced gates. Substitution `r=ell+t` gives `t²+ell*(2*t−k)` as an exact
identity over integer rings. If the new positive graph vanishes then its
parent graph vanishes under that substitution. Conversely, at a parent zero,
the inherited unit-factor result gives `r²=ell²+ell*k+1`. Positive `ell`, `k`
and `r` imply `r>ell`, so `t=r−ell` is positive. These maps are inverse on
zeros and retain all other coordinates. We rely on the parent result under
its stated `beta>0`, `K0>=0` hypotheses, with arbitrary integer `MC`, `MF`;
this review does not reprove its negative-Pell descent or the endpoint chain.

The independent checker verifies the complete 74-to-75 gate edit and
topology, input and gate liveness, the sparse formal polynomial identity,
and that the substitution cannot affect the other gates. For the upper bound,
it checks the polynomial cancellation used to bound `F1` by degree 30,
verifies its graph shape and the necessary source degrees, and then propagates
degree bounds through all remaining gates. For the lower bound, it hashes and
decompresses the fixed ports against the pinned independent binding records,
then computes the 97th finite difference of the `t=2x`, other inputs `x`
ray modulo 1,000,000,007. Its nonzero leading coefficient is `979034495`.
This procedure differs from the candidate checker's coefficient propagation.

This is not a Lean elaboration, an iPRA derivability or proof-existence
theorem, a proof that the graph describes the PDF or physical files, or an
independent replay of the foundational providers. The finite executable
checks support the named algebraic and graph claims; they do not by
themselves prove the inherited unbounded arithmetic arguments.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-shifted-pell75-independent/check.py | cmp - reviews/ordinary14-shifted-pell75-independent/result.json
```

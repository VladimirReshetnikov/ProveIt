# Independent review: unshifted-s obstruction for the natural-79 graph

The [78-operation probe](../../research/ordinary14-natural78-unshift-s-obstruction/README.md)
has the claimed natural zero with `s=0` at the documented toy and externally
authenticated compact ports. At the stated toy input, the 79-operation parent
is nonzero at the same vector. Thus a universal forced-positivity argument for
`s` and that particular unchanged-coordinate transfer are false. This does not
prove different **global** zero-existence truth values, a consistency theorem,
Lean/iPRA derivability or a PDF binding.

For `beta>=2`, `K0>=0`, `MC>0`, `MF>0`, the stated positive `w` satisfies
`w≡1−K0 (mod beta)`. With `q=beta+1`, the numerator `q*w+K0−1` is nonnegative
and divisible by beta. The defined rank is positive, so the proposed shifted
inputs and the quotient slot are natural. When `s=0`, the graph has
`Y=U=ell=0`, `c=1` and its shift-rank term vanishes. The stated `f=2`, `i=3`,
`r=y=1` give all four restricted factors equal to +1. Since `F=1` and
`alpha=beta−1`, `C=1`; the chosen quotient makes the guard +1 as well. All
five factors therefore multiply to one. The direct `w` and `gamma` slots in
this graph are handled explicitly in the witness.

The independent checker pins both graph JSON files, verifies all 78 surviving
DAG rows, the exact single shift deletion, topology and liveness of every
input, port and operation. It evaluates all gates at the claimed toy vector
and checks the parent is nonzero at that same vector; it also checks two
additional toy cases. It independently authenticates all four P72 compressed
and raw payloads against the pinned P72/P115 binding records using zlib's
gzip decoder, reconstructs their little-endian integers, and evaluates every
probe gate at the resulting large witness. The original checker and this
receipt both reproduce. Those file checks are external and do not establish a
Lean-to-file theorem or PDF semantics.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-natural78-unshift-s-obstruction-independent/check.py | cmp - reviews/ordinary14-natural78-unshift-s-obstruction-independent/result.json
```

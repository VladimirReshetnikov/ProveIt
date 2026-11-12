# Independent source review: model rank lower bound

The bound `R>=40` follows from exactly the displayed scalar hypotheses `F>0`, `alpha>0` and `F+alpha<q`, with MC, MF and J natural. They imply `q>=3`, `q-1>=2` and `q-F>=alpha+1>=2`; hence `(q-1)(q-F)+alpha>=5` and `q²-1>=8`. Their product is at least 40, and the remaining rank summand is nonnegative. The bound 40 is attained in the finite control at q=3, F=alpha=1 and zero remaining summand.

The source explicitly proves the needed lower bounds before using truncated-subtraction cancellation for `q-1`, `q-F` and `q²-1`. Its `mul_le_mul` side arguments are nonnegativity of the lower right factor and upper left factor, and match the displayed uses. The graph specialization matches the pinned 90 natural-rank definition and retains its positive-C gap as an explicit premise; the 26-bound is a direct weakening of 40. No eta-zero graph or physical compact-port assumption is supplied here.

Source signatures and finite controls were independently checked; the author's receipt reproduces. This does not elaborate `omega`, casts, natural-model arithmetic, imports or providers, establish the graph's positive-C gap, or supply the exact-index or iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-rank-lower-model-independent/check.py | cmp - reviews/ordinary13-residue-rank-lower-model-independent/result.json
python3 -I -S -B research/ordinary13-residue-rank-lower-model-draft/check.py | cmp - research/ordinary13-residue-rank-lower-model-draft/receipt.json
```

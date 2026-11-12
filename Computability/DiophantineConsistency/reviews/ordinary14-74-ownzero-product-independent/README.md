# Independent review: 74 own-zero product extraction

**PASS at source and exact signed-pair algebra scope.** The literal 74 product
orders the factors first, main, auxiliary, strong, guard. Its output is that
product minus one. The proposed `pairEval_mul` and `one_of_zero` repeat the
existing signed-pair interfaces: evaluating multiplication gives pair
multiplication and the split-natural zero of `e−1` gives equivalence of the
pair of e to natural one. The exact `swap_last` identity correctly moves guard
to the unrestricted fourth slot required by `first_factor_units`.

The conditional unit theorem invokes the first-factor client at the same
ports and valuation, retaining the beta cast, beta/J/w/s positivity and
main/auxiliary/strong residue exclusions explicitly. The checker verifies the
literal output rows and source signatures, checks the pair swap for 59,049
natural-pair assignments and subtraction-of-one behavior, and independently
checks a nonvacuous first Pell unit and the four remaining signed factors. It
replays the author receipt.

This is a source-level review: proof tactics and imported drafts are
unelaborated. The three residue exclusions are not derived from the graph
here, nor are guard strictness, 74↔75 model equivalence, coherent providers,
the iPRA endpoint, or physical byte/PDF binding established. No Lean run was
performed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-74-ownzero-product-independent/check.py | cmp - reviews/ordinary14-74-ownzero-product-independent/observation.json
```

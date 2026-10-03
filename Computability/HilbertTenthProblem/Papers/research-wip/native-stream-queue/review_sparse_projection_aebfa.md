# Independent check of the sparse-lattice wire projection

PASS on `sparse_lattice_projection.py` SHA256 `bfa23f92958b6beb1a8a782ea2d478257d4d11b52f4d5559509913d21082e950`, applied to original `sparse_mass.py` SHA256 `1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8`.

Read the complete core theorem, its natural-zero proof and ledger, the actual `Builder.layer`, row-lookup and sorting code, the fixed-history constructor, and the full projection helper. This is a bounded review of the projection, not a second review of the full substrate archive or its source-machine universality.

For the row-selector backend, remove `M` streamed-position wires, `3M` incoming-mass wires, `3M` output-mass wires, and two maximum-output wires from each of the `M(M−1)/2` sort comparators in every layer. All have monic defining residuals and strictly earlier dependencies. Retain all channel/table selectors, comparison flags/slacks, and minimum-output wires.

The substitutions preserve degree at most two. Streamed positions, outgoing masses, and maximum outputs become affine expressions. In particular, a maximum output stays affine even through a chain of compare-exchanges because the minimum output remains a supplied coordinate. Incoming masses become quadratic products of equality flags and channel selectors, and inspection of the actual emitted source confirms that their only surviving consumers are linear table-input moment equations. There is no multiplication of those substituted quadratic expressions by another variable.

Restoration is nonnegative at every new natural zero by a layer induction. The fixed initial row is a genuine shifted configuration. At layer `t<T`, true prior positions are at least `T−t≥1`, so the streamed positions are nonnegative. Retained comparisons force the true equality flags; therefore incoming masses are sums of nonnegative selector products. The table simplex forces the correct nonnegative output masses. Rank comparisons give genuine channels. For each sorting comparator the forced bit and retained minimum rows choose one real nonnegative input; its restored maximum is exactly the other input. This gives a valid next row and closes the induction. The argument does not assume every restored expression is nonnegative on arbitrary nonzero tuples.

With `S` allowed table rows, the projected default-natural ledger is

- `V = T[M(S+7)+4M(M−1)]` coordinates;
- `R = T[10M+4M(M−1)]` residuals;
- `T[7M+M(M−1)]` coordinates and defining rows removed.

The orthant-exact option adds `2MT` residuals. Endpoint rows remain separate; a mass mismatch contributes the original constant-one row. Restricted tables retain their existing trajectory-coverage obligation. The stated counts are not those of the separate factorized lookup backend. `T=0` remains an empty witness tuple.

On the restoration graph, every removed residual is the zero polynomial and every retained residual is its literal substituted old row. Hence the complete original and projected sums of squares agree on **all integer tuples** on that graph. The natural-zero bijection additionally uses the induction above. No operation-count saving follows merely from fewer wires: expansion can make affine forms and residual lists larger.

The independent portable checker reconstructs every substitution and residual with its own sparse polynomial implementation, rather than reusing the producer's polynomial arithmetic for those identities. It checks the entire expanded SOS equality in seven emitted instances spanning `T=0`, masses1/2/3, both orthant settings, full/restricted tables, endpoints, and large initial gaps. It also checks every incoming-mass consumer and all restored degrees. The receipt records 542 assertions, including seven complete symbolic SOS identities and 54 exact consumer checks.

```sh
python review_sparse_projection_aebfa.py \
  --source /path/to/sparse_lattice_projection.py \
  --producer /path/to/original/sparse_mass.py \
  --output /path/to/new.json --expect review_sparse_projection_aebfa.json
```

Both executable sources are authenticated before import; the helper rejects disabled assertions and uses no hardcoded workspace paths. No repository or archive files were modified by this review.

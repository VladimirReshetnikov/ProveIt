# Reproducing the new reduction

The principal candidate is `u208.native.tm`; `u208.tm` is its dense relabeling.
The parent is the Joint U209 native machine with SHA-256
`d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16`.
`local_proof.md` gives the entire mathematical reduction, and
`local_certificate.json` records the four whole-tape local paths, complete
incoming inventories, and all 414 commuting rows.

The readable standalone discovery program takes a transition-table path and
an output path explicitly:

```
python3 discover_folds.py /path/to/u209.native.tm --output discovery.json
```

Its defaults are history depth 3 and maximum local block length 7. They
already recover the new reduction. The two reported orientations delete
172 in favor of 211, or delete 211 in favor of 172; these differ only by the
name retained for the common state. The intended main construction uses the
first orientation and replaces 211/read-zero by `0 L217`.

The discovery program uses incoming-history bit cylinders to overapproximate
reachable local tapes. It screens possible folds by finite random runs and
accepts them only after exhaustive symbolic execution on every cylinder.
The final elementary proof does not depend on randomness or on the discovery
program; it needs only the complete incoming-edge inventories and four
short literal paths.

For the larger original discovery scope use `--depth 8 --limit 31`.
This examines 458 oriented compatible-row pairs and 379,224 replacement-row
choices on Joint U209. It again finds only the two orientations above.
A separate negative search on U208 (history depth 8, macro bound 31) examined
448 oriented compatible-row pairs and 369,152 mutations with no accepted
additional fold. These bounded negative results are not minimality claims.

`u208_compatibility.native.tm` is an optional second construction, obtained
from the distinct Compatibility U209 by the same reduction with helper 214
in place of 217. Its local proof is the main proof with the local state
correspondence (163,217,215) -> (216,214,163). It has not been selected as the
principal candidate. Its finite local paths are in
`compatibility_local_certificate.json`.

Preliminary scripts `context_alias.py`, `context_fold.py`, and `double_fold.py`
were scratch discovery work. The last merely proposes structural patterns
and does not validate them. They are not needed in the final deliverable.
Use the standalone discovery program above and the independent final local
checkers instead.

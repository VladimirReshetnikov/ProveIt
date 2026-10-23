# Attribution and source boundary

The source repository is Vladimir Reshetnikov's `ProveIt`, at commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`:

https://github.com/VladimirReshetnikov/ProveIt/tree/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms

The new construction builds on these explicitly credited components:

- Package 59, `nine_free_adjunct`: complete source, source packing, free
  carrier, exact CRT parameterization, quotient shift and norm finalizer.
  `build.py` is adapted from its `build_nine.py`.
- Package 59, `sun/circuit.py`: retained integer arithmetic DAG support.
- Package 59, `encoding/verify_split.py`: adapted as `check_source.py`;
  local data paths are used and the authenticated base floor is 2^2134939.
- Package 48, `proofs/HIGHER_MAJORANT.md`: polynomial quotient approximation
  and the elementary square-root majorization argument.
- Package 55, `nine_majorant`: polynomial ring checking pattern and the
  two-defect norm expansion. `check_exact.py` adapts its sparse polynomial
  engine to a new three-variable certificate and new exact identities.
- Package 31: complete native coefficient/compiler adapter and original
  positive source. The four original31 payloads are copied, without changes,
  from package 32's compiler directory. They are never mixed with another
  tuple.

The new mathematical content is the exact deflation using the actual
Pell-parameter relation, the seventh-order majorant, its complete
positive-coefficient certificate, and its resulting nine-variable degree
tradeoff. The new code and proof were produced with AI assistance in this
research session. The native compiler and K215 endpoint remain inherited
theorems; finite checker success does not independently formalize them.

`SOURCE_PINS.json` distinguishes verbatim source copies from adapted files
and records both original and delivered hashes. The upstream license and
notice files are retained under `licenses/`. The original31 binding embedded
inside `coefficients/BINDING.json` is historical provenance: its nested path
strings refer to the original package. The outer payload list, aliases and
local adapter path are the operative references in this package.

# Independent audit of positive transport and direct-BFS raw columns

The captured read-only check inspects three selected guarded author receipts:
positive transport, direct-BFS coefficient decomposition, and direct-BFS
raw-column decomposition. It checks current and archived sources, runners,
Lean tool, selected listed objects, logs, axiom targets, 10 resolved direct
imports, five retained terminal histories and 12 sampled resource observations.
The raw-column producer selects the exact coefficient-decoder object recorded
by the accepted author receipt. Earlier direct-BFS decoder, mass and band
objects match their prior audit hashes. This is not a Lean replay or a full
transitive serialized, package, dynamic-library or historical source-to-object
ancestry audit.

One of the ten direct imports is **not individually pinned** by its producer:
`DirectBFSCoefficientDecoder` imports
`DiophantineConsistency.ArithmeticWindowCarry`, but its runner omits that
object from its explicit pin list. The audit resolves it after compilation to
`/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticWindowCarry.olean`,
SHA-256 `91006702f70eed7c45b603b7e0dd113fb4c319a5a200cc0f7b8707303dd0121a`.
This post-hoc hash does not authenticate the compile-time bytes. The raw-column
runner itself pins its selected coefficient-decoder object at
`/tmp/direct-bfs-coeffdecoder-pi1psx0a/DirectBFSCoefficientDecoder.olean`,
SHA-256 `65cd43565f97f44b682112865e52de09543c79505b4ed0e2c85ac3fa3043e583`,
and its other direct imports; it nevertheless inherits the upstream omission.
This is a provenance boundary, not a demonstrated theorem error.

For an actual positive 80-graph zero and the symbolic β, low-mask and
shifted-high-mask port equalities, `graph_positive_transport` gives `q < v₅`
and a **positive** t together with `Cnat > 0` and
`(p₁+v₅)*Cnat = v₁+b*t`. The same graph variables are used throughout, and
p₁ is arbitrary. Its proof recovers the actual graph power and rank bound,
then excludes t=0 using the natural transport equation and the graph mask
gap. It is a necessary graph-zero consequence, not a first-factor zero or
a source/graph converse.

The coefficient decoder lifts the direct table's finite coefficients to the
corresponding model tile values and proves the finite selector/copy sum
identity. The raw-column result uses that direct-BFS family to decompose
both band columns and the full indexed raw column into two direct decoder
forms, bare contribution and temporal digit. Its `band_column` and
`decoder_bands` require `0<n`, `k<n` and `C<2^(67*n)`; `flatten` is the
separate algebraic identity. These do not assert a graph-derived decoder
window, tile/color conjugacy, machine equivalence, external file binding or
iPRA theorem. Printed Lean axioms are metatheory dependencies.

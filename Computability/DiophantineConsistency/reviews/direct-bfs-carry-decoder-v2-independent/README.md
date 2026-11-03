# Independent audit of corrected direct-BFS decoder and parity chain

The captured read-only check passes for four corrected guarded author builds:
the coefficient decoder, raw-column decomposition, raw parity and 80-graph
simple parity. It checks current and archived source, v2 runner and Lean
hashes, selected listed providers, logs and reported axiom targets; all 11
resolved direct imports are individually pinned. Nine retained terminal
histories and 16 sampled resource observations are inventoried. This is not
an independent Lean replay or a complete transitive serialized, package,
dynamic-library or historical source-to-object ancestry audit.

The coefficient-decoder v2 runner individually pins its previously omitted
direct import `ArithmeticWindowCarry.olean`: the selected object is
`/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticWindowCarry.olean`,
SHA-256 `91006702f70eed7c45b603b7e0dd113fb4c319a5a200cc0f7b8707303dd0121a`.
The raw-column v2 build selects the fresh coefficient-decoder object at
`/tmp/direct-bfs-coeffdecoder-pkx85n9l/DirectBFSCoefficientDecoder.olean`;
raw parity selects `/tmp/direct-bfs-rawcolumn-wnhkwnl1/DirectBFSRawColumn.olean`;
and graph simple parity selects
`/tmp/direct-bfs-rawparity-jmkuze4q/DirectBFSRawParity.olean`. The selected
paths and object hashes match the corresponding corrected receipts. All four
new outputs are bit-identical to their earlier accepted versions and use the
same Lean source hashes. This repairs the specific individually unpinned
direct-import boundary documented in the [earlier review](../direct-bfs-raw-column-positive-transport-independent/README.md).

The generic raw-parity result assumes `0<n`, `k<n` and `C<2^(67*n)`; it
reduces its raw column modulo two to the two direct-selector sums, bare term
and temporal digit. The graph simple-parity theorem assumes a positive
80-graph zero and all four symbolic ports, including direct-BFS `p₁`. It
reconciles two obtained radix lengths by internal exponential injectivity and
concludes the anchor-column parity and carry bounds at one N for the graph's
own residual power and direct selector family. It does not establish a full
selected-row decoder, machine/color conjugacy, either direction of a whole
graph equivalence, external JSON/PDF binding, or an iPRA endpoint. Printed
Lean axioms concern metatheory dependencies.

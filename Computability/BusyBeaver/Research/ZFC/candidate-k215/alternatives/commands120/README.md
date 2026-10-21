# A 215-state machine with DROP/NIP/MP command order

This is Source 160's distinct command-order alternative, accepted after a
fresh complete symbolic runtime and blank-start check. Its ordinary proof
establishes in ZFC that blank nonhalting is equivalent to Con(ZFC). It has
215 working states and 430 transitions. The repository's
[primary K215](../../README.md) retains NIP/DROP/MP order; neither construction
establishes a214-state result.

The source uses DROP0/NIP1/MP2 and AX tags starting at 3. It combines the
command-local field reads of the
[permuted216 predecessor](../../../candidate-k216/alternatives/permuted/README.md)
with the partial selector and 164/183 marker fold. The source has 202 distinct
subtrees,4,751 primitive occurrences and 6,175 guarded successor edges plus
halt. Both source resolvers prove complete ordinal-graph identity to the
corresponding120 predecessor, for arbitrary natural registers.

| Artifact | Meaning |
|---|---|
|[k215.native.tm](k215.native.tm)|Native table: start0, dispatcher 84, halt254|
|[k215.tm](k215.tm)|Dense table: states 0–214, dispatcher 84, halt215|
|[canonicalization.json](canonicalization.json)|Complete state bijection|
|[sites215.json](sites215.json)|Compact ordered primitive source|

Native SHA-256: `da83e8de52f4d9536cee2d5ed4af4311308bda51196d18891b96e4bc9ca6cb4f`.
Dense SHA-256: `2a286a61782130f9c1d1c3a0f9e546108a4de321b3f80d3b53dc3a9f14ece447`.
Source SHA-256: `d5c994e3d0c8fe26dd337aca48e5f25ff4f28fd18973f2c04c99589d6ba3f53d`.

The fresh runtime proves all 6,176 cases with 1,698,845 symbolic rules, minimum
positive affine duration 9 and coverage of all 430 rows. Its complete blank
initialization takes96,284 transitions and reaches dispatcher 84, head−8,
header 57, gap 1, registers `[4,0,0,0,0,0,0,0,0]`, forty unit spares,95 one-cells
and zero exterior. The independent saved-output audit checks every recorded
event against both table formats and verifies the complete frame.

The ordinary numerical-calculus, strong compiler and cofinal cutoff 4 proof
are inherited from Source 159; the new full-source and physical-fold arguments
are reviewed separately. The final all-tape fold compares the constructed
pre-fold216 to this215, with positive1/3-step blocks. No exact-table Lean/PA
endpoint, unconditional nonhalting or minimality is claimed.

[Batch198 review, proof and attribution](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-198.md)
and [recovery/reproduction](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-198-reproduction.md)
preserve the original Source 160 archive at 001695a82b, both construction
recipes, all fresh raw evidence and inherited notices. Credit belongs to
that submitted ChatGPT-assisted ProveIt composition and its named antecedents;
the repository's independent120 allocation is separate.

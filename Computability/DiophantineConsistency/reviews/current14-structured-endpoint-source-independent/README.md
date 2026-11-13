# Source review of the structured-port endpoint draft

The reviewed [`StructuredEndpoint.lean`](../../research/current14-structured-endpoint-draft/StructuredEndpoint.lean)
has SHA-256 `31b2869c63f33610beac36cec7bcbcbcbfc00579b106fbc130ce0f754702a392`.
No concrete logical or tuple-wiring defect was found by source inspection.
No Lean process was run and the draft remains **unchecked**.

The existential `p : Fin 4 → ℤ` is a Lean-level witness shared by the four
recipe comparisons and the iPRA derivability statement. The proof selects
`CurrentWindowCarry2011.ports` and uses `Current14LiteralPorts.all_ports`
for slots 0, 1, 2, 3: β, rationally cast K, μ, ω. The same `p` is passed
to `noZeroAt`; the theorem does not assert an existential tuple inside iPRA.

`noZeroAt` applies `positiveShift` to `expressionAt p` and constructs the
same pair of split-natural terms, language embedding and mapped refutation
predicate used by the existing `noZero14` endpoint. On the selected tuple,
the current source defines `naturalExpression` as `positiveShift expression`
and `expression` as `expressionAt CurrentWindowCarry2011.ports`, so the
proposed `change` is the intended definitional identification. Its actual
elaboration, kernel memory use, exact imported objects and Lean result have
not been tested. The source concludes the native mapped-refutation negation
used by `IPRAStandardCurrentEndpoint.ipra_current_iff_consistency`.

The 61-module source extension prepares the two project imports of the
printed-port assembly; that assembly and this draft each require their own
subsequent same-provider compilation and guarding. A successful source
review does not establish a coherent join, formal TeX/PDF or compressed
payload semantics, or the transitive provider ancestry.

Other inspected source SHA-256 values:

| Source | SHA-256 |
| --- | --- |
| `Current14LiteralPorts.lean` | `b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0` |
| `CurrentEquationSyntax2011.lean` | `112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7f5c776a3db3` |
| `IPRACurrentNativeZFC.lean` | `3d3180937e6b040dd9630866f328b641f2bb40494f784d5ee5be0ce6f0edffcc` |
| `IPRAStandardCurrentEndpoint.lean` | `756d87adb5a9cb8e192156b043714f55afe3836d7833ef87d5113cba8d772c38` |
| `CurrentKernelData2011.lean` | `529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c` |

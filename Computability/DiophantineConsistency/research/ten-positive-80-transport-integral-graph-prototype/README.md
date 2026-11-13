# Natural integral transport for actual 80-graph zeros

`Direct80TransportIntegralGraph.graph_integral_transport` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph admits a natural `t` with signed graph transport `B=ι(b*t)`, under explicit `beta≥31`, `MC<beta`, `MF<2*beta`, and internal odd-beta hypotheses. It derives the sign and divisibility of B, rather than assuming an integral or nonnegative transport quotient.

The proof combines the actual signed integral carrier, exact carrier identity, graph unweighted `H∣Kpos` quotient, and signed `μ²∣e` quotient through the separately checked domain cancellation lemma. It justifies all natural subtractions when binding `Hnat` and `Knat` to their ring expressions, proves μ² and H nonzero, and transfers the resulting signed divisor to a natural quotient using model nonnegativity. It does not assume any coprimality of Y with b or cancel a selected projection factor.

Guarded author `observations/graphpower-attempt01/` passed without diagnostics, producing `/tmp/tenpositive-80transport-integral-graph-n8_ti136/Direct80TransportIntegralGraph.olean`, SHA-256 `496abceb22539866edf651561897294f49c449aa0c7c69b050f682969e2acfd1`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned; complete transitive project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

The explicit symbolic port assumptions still require specialization; this theorem does not itself prove the remaining native fraction reconstruction, graph-to-halt equivalence, or iPRA endpoint.

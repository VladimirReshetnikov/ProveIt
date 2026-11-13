# Independent review: 80-graph height and whole-product projection

For an actual positive zero of the exact Lean 80-row graph, `graph_entire_product` proves in the model **difference ring**

`H ∣ b * (X − 2^R) * (2^R * X + 1)`,

where `H=4A−1`, `b=beta*J`, and `R=rankNat`. Its explicit port assumptions are beta positive, `MC<beta`, and `MF<2*beta`. The expression is in the difference ring because `X−2^R` can be negative; the theorem does not use a natural truncated difference for that factor.

The signed carrier identity first gives `H ∣ b*K` in the difference ring, using `H=mu*t−1` to cancel the particular factor `mu²`; it does not cancel `b`. The natural projection theorem justifies both truncated subtractions in `Hnat=4A−1` and `Knat=X*(3c−2X)+2` using graph positivity and `2X<3c`, and transfers `H∣b*K` into natural divisibility by splitting the sign of its quotient. The Pell packet uses the graph's actual `rankNat` for its main ordinate and the all-index projection quotient, obtaining natural witnesses with `d=2^R+(A−1)c+H*z` and the norm for the same `d`.

The abstract whole-product ring argument keeps the factor `b` in each intermediate and in the conclusion. It first derives `H∣2*b*K'` from the given projection divisor, then cancels only the factor 2 using the explicit identity `1=H−2*(2a+1)` for `H=4a+3`. The Pell norm supplies a second divisor, and a ring identity combines the two into the entire product. The graph binding embeds the natural Pell and divisor witnesses and rewrites the justified subtraction; no arbitrary cancellation of `b` is used.

The separately checked graph height theorem proves `2^R<Y` under stronger assumptions `beta≥15`, odd beta, and the two port bounds. Neither the height result nor the product theorem proves that the whole product has absolute value below `H`, that a factor is zero, or that `X=2^R`. A further bound and fixed-recipe integration remain necessary, along with graph-to-halt and iPRA proofs.

The captured `check.py` verifies six successful author producer receipts, current source/runner/Lean and output hashes, selected predecessor pins, direct-import resolution and matching producer objects, diagnostics, axiom reports, and sampled resources. It verifies the archived source/log artifacts for nine historical terminal receipts and the two failed staged product attempts. The broad-import product attempt01 was terminated; attempt02 failed to elaborate; neither is promoted. Detailed hashes and selections are in `observations/attempt01/stdout`.

This is a read-only audit without an independent Lean replay or reconstruction of the complete transitive project/package/dynamic and historical source-to-object ancestry. Axiom reports are Lean metatheory dependencies, not object-theory iPRA axioms. Resource observations are sampled; external graph/PDF correspondence remains separate.

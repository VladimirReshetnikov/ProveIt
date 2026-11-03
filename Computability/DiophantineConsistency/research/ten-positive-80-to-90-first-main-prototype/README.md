# Actual 80 zero gives simultaneous 90 first/main factor zeros

`TenPositive80To90FirstMain.graph_main_factor` proves that an actual positive
80-graph zero in an IΣ₁ model, with the symbolic β/low/high port equalities,
yields **one shared** positive fresh η, ζ, γ, s and a natural h such that,
for every positive t₀, T, n, the valuation

    [v₀, v₁, v₂, t₀, T, v₅, v₆, s, η, ζ, n, γ+h]

is positive and zeros both the selected 90 Lean graph's first and main
factors. The proof selects the positive transport quotient and the fresh
Pell witnesses together, uses the exact selected first-factor recipe, and
reuses the same η, ζ, γ and h for the main factor. The three universally
quantified coordinates remain available for the ordinary factor. Port p₁ is
arbitrary; no external K0 byte string is identified.

The ordinary factor has not been zeroed. Accordingly this result does not
prove an 80-to-90 full graph implication, graph equivalence, halt equivalence,
PDF binding, or an internal iPRA theorem.

The accepted guarded run is `observations/join-attempt03/`; it produced
`/tmp/tenpositive-80to90firstmain-a7w5txwk/Direct80To90FirstMain.olean`,
SHA-256 `b321f85364992b1a8da7221e3682a4fa951bce2d85e46bb938bf890c98d6e159`.
Attempt01 was a deliberately incomplete scratch snapshot containing `sorry`
and was rejected. Attempt02 produced an object but failed the runner's
unused-variable warning check; it is not the accepted check. The successful
source contains no `sorry` and the receipt pins the corrected v2 first
coordinate producer, selected direct factor providers, tool and resources.
Project/package, dynamic-library and transitive historical source-object
boundaries are inherited.

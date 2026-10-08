# Further research agenda

Full discussion appears in Section 12 of the article. None of these questions
is assumed in its proved theorems.

## Highest-value algorithmic next steps

1. **Persistent higher-rank normal forms.** Implement the exact canonical-state
   primitives in Proposition 11.1, including comparisons and shared storage.
   Test both the central sleeves and the rank-two geodesic barrier.
2. **Bounded length-preserving rewriting.** Escape the proven strict-shortening
   barrier through coherent Artin/commutation moves with an explicit search
   budget and a charged potential. Prove a nontrivial structural-class bound.
3. **Event-driven saturation.** Replace repeated full passes by local updates
   without invalidating the globally optimal prefix scores. Find an amortized
   bound or a forcing example.
4. **Production ablation.** Run the real gateway smoke test and full upstream
   recognizer, measuring both beneficial and no-op inputs, peak memory, resource
   exits, reduced crossing counts, and paired end-to-end times.

## Structural extensions

5. **Longer finite target sets.** Extend the rank-two optimizer beyond radius
   one, deduplicating equal targets and bounding its radius-dependent cost.
   This alone cannot overcome the geodesic barrier.
6. **Nested inflation depth.** Recover layered decompositions without receiving
   them as witnesses. Analyze whether optimal-pass tie choices preserve a
   promised hierarchy or whether another search policy is needed.
7. **Compression parameters.** Relate the observable one-pass residual size to
   structural diagram or braid invariants under explicit hypotheses. Do not
   identify it with geodesic length: the barrier disproves that equality.
8. **Certified patches in general diagrams.** Extract braid-like local patches
   with endpoint order, overlap bounds, and honest conversion costs.
9. **Alternating braid equality and Markov descent.** Keep context-safe equality
   witnesses distinct from closure-preserving witnesses and seek a geometric
   decrease of a well-defined complexity measure.

## Homological and topological routes

10. **Succinct complex representations.** Support exact closure/rank operations
    on symbolic tensor or multiplicity structures without expanding the basis
    prohibited by the survivor theorem.
11. **Stronger representation lower bounds.** Use multiple closure functionals
    to test tensor rank, decision-diagram width, or other compressed models.
12. **Certified scan-order look-ahead.** Choose an order that avoids difficult
    prefixes while bounding both search cost and the entire intermediate state.
13. **Costed hierarchy operations.** Implement one nontrivial topological
    cutting or reduction primitive with encoded input/output, bit-size bounds,
    provenance, and exact operation accounting.
14. **Formal verification and porting.** Formalize quotient/exponent injectivity,
    trie states, prefix optimization, and replay. A Rust port should match exact
    outputs and certificates against the Python oracle before timing claims.

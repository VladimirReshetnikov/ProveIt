# Independent review checklist

1. Check the intrinsic grading convention k-c(a,b)+2|S| against the exact
   Frobenius/cobordism conventions, with quantum shifts explicitly forgotten.
2. Check derivative compatibility with both saddles over F2; do not assume
   cup/cap naturality or carry the argument into another characteristic.
3. Verify the nested-matching round-trip product and the additional dot,
   including k=1. Confirm that the proof is not based only on small examples.
4. Verify central marked-dot decomposition, and distinguish B's radical index
   2k-1 from H's index 2k.
5. Check that scalar residue is taken only between equal matching types.
   Off-diagonal undotted morphisms are radical, despite having low bit 1.
6. Check the scalar contraction and all transferred homotopy identities, with
   matrix multiplication order as implemented. Block units are not involutions.
7. Check the off-by-one distinction between inverse-series depth and the last
   differential correction. The six-object example detects premature truncation.
8. Confirm when input-square validation is excluded from the output-sensitive
   cost. Account separately for full homotopy certificates and cache memory.
9. Re-run independent braid/cube comparisons and then the complete upstream
   tests in an actual checkout before modifying a default.
10. Benchmark hard unknots and inputs reaching Khovanov after current filters.
    The raw local timings do not answer this deployment question.
11. For any global complexity claim, supply scan-order search, representation,
    multiplicity, transformation, and topology-verification bounds. Check that
    a timeout is not interpreted as a verdict without a proved global cover.
12. Audit novelty against the arc-algebra and minimal-complex literature before
    making any first-in-literature claim.

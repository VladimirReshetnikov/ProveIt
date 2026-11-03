# Independent 80-row adjacent-descent review

The seven accepted packets form the following chain in every IΣ₁ model with
the repository's `ORingStructure` interface:

1. The denominator lemma uses `m>0`, the explicit signed natural Bézout
   certificate `Bez r m 1`, and a cross-multiplied norm to prove `m² ∣ B`.
2. Preservation and bounds establish reducedness of the reflected numerator,
   norm preservation, and strict decrease of a positive first coordinate.
3. The assembled step uses `B>0`, `m>0`, `v>1`, the certificate, and the norm
   to produce a smaller positive coordinate with the same reduced denominator
   and norm. Signed expressions are handled through magnitudes.
4. The complete theorem defines a Σ₁ predicate for positive coordinates,
   invokes the model-internal least-number principle, and uses the step to
   force its least witness to one. The norm and Bézout certificate then imply
   `m=1`.
5. The scaled-norm theorem constructs the internal gcd certificate itself and
   derives an integral quotient; callers do not assume reducedness or scale
   divisibility.
6. `Direct80Adjacent.graph_adjacent` supplies the hypotheses from a positive
   zero of the actual 80-row Lean graph with arbitrary natural ports and
   `beta>0`. It concludes the positive roots and adjacent Pell quotient
   stated in the source, representing the signed graph values by squares of
   model elements. It does not assume a sign for those values.

The retained independent check verifies the seven accepted source snapshots,
object hashes, logs, allowed axiom reports, resource samples and pinned
prototype objects. It also inspects 16 earlier attempts, distinguishing
failures, smaller intermediate proofs, and a warning-rejected zero-exit run.
Current direct-import resolution and relevant 90-provider objects/companions
are checked separately; these checks do not retroactively add historical
guards to the author runs.

No mathematical or receipt mismatch was found in this review. The result is
a necessary arithmetic consequence of an actual graph zero, not a reverse
witness construction, fixed-port machine equivalence, iPRA derivability, or
Lean binding of JSON/PDF bytes. The captured audit exited zero with empty
stderr and did not replay Lean. Full package-transitive, dynamic, and
historical source-to-object ancestry remain inherited; resource samples are
not continuous.

# Proof review and source reconciliation

## Elementary quotient proof and characteristic corrections

This pass reviews the maintained ring definitions and thirteen standard
results from `osq:lem:ct` through `osq:thm:universal`, together with
`osq:cor:nofield` (the deferred proof of `osq:prop:fractions`(iv)) and the
positive-characteristic shortcut `osq:rem:poschar`. It checks the local
support and Hartogs conventions needed by these proofs. The later
classification theorems, cross-report group-theoretic consequences,
class-ultrafilter foundations and full reconciliation of the parallel
source manuscripts remain pending. This is a manuscript review, not a
Lean proof or a literature/priority certification.

The unrestricted integer-divisibility clause of `osq:prop:common`(iv) was
false over arbitrary coefficient fields. For characteristic p, pΠ_k = 0,
whereas the monomial X^a is a nonzero member of Π_k for a > 0. The corrected
clause requires the integer to have nonzero image in k; multiplication by
every nonzero coefficient is still a bijection on the support ideal.
The corresponding shortcut for a target killed by n now requires n ≠ 0
in k. It works for characteristic-zero coefficient fields and positive-
characteristic targets, including maps from Oz and its Gaussian ring.
When source and target both have characteristic p, the full collision
proof is still available, but division by p is not. Ordered exponent-group
multiples na are distinct from these coefficient scalars.

The proof of `osq:lem:separation`(iii) used the direct module argument
without carrying its commutativity assumption. Its statement is retained:
for noncommutative sources, apply the ring assertion to the set-sized ring
End_Z(M). For commutative sources the direct orbit argument gives the
sharper comparison with |M| itself. This distinction matters later for
exact cardinal thresholds; an endomorphism ring can be much larger.

The support proofs now verify ring closure and surjectivity of the
retraction, spell out why the small-exponent interval is a proper class,
handle empty support families, and prove both inclusions in the directed
union and ideal-square identities. The scale-field lemma writes its
ordinal-indexed family explicitly with the parameter a and uses a Hartogs
restriction to prove proper-class size. Hahn inversion is read in the
set-generated exponent subgroup. The weighted telescope treats equal
exponents as a separate case with its positivity hypothesis retained;
its leading coefficient is checked explicitly. Zero members of a packing
family use zero quotients. The universal proof uses only a set restriction
of an explicit class map and explains the action on the vector hv when
passing from monomials to the whole ideal. No infinite sum is transported
through an arbitrary homomorphism.

The report's assertions that the repository has no omnific Lean modules
are obsolete. Its current text and guides acknowledge the actual rings
and shared support, degree, unit, divisor and ideal results already mapped
through the sibling report. The full-class quotient and later cardinal
results still require their own proofs and size interface.

The ledger's opening count is corrected from 415 standard statements plus
three principal summaries to 409 standard statements plus nine principal
summaries. All 418 statements were already present, and the standard
inventory already counted 409, so the collection total remains 4,626.
The older mixed count in review records does not describe the current
source environment counts. The nine principal-summary anchors are also
refreshed from the source.

Validation: the unchanged source-06 verifier passes 17,586 exact checks,
and source 11 passes 1,858, both with their fixed default seeds. These
check finite remainder identities, support inequalities and coefficient
algebra (plus their existing derivation/matrix examples); they do not
prove infinite summability, proper-class size or the universal theorem.
Three-pass builds of the 262-page article and 33-page catalogue are clean.
All 828 source labels and 1,656 auxiliary label numbers are preserved.
Only four standard statements change text: the corrected integer clause,
the set-sized qualification on cardinal notation in scaled-field collision,
the explicit scale family, and the separate equal-exponent weighted case.
All nine principal summaries are unchanged. No Lean or shipped verifier
source changed in this pass.

The changed proof and catalogue pages were inspected visually. The refreshed
4,626-result index across 63 reports, 5,194 source references, 1,743 local
Markdown destinations and whitespace checks pass. The existing full Lean
build remains the baseline for this documentation-only revision.

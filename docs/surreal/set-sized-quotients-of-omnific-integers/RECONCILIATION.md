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

## Synchronization with Pell and principal-ideal formalizations

Merged `c0dd3be`, including `55338a0`. The new statements were compared with
`odg:def:cor:pell`, `odg:def:lem:pelldiv` and `odg:def:lem:intmultiple`.
Intermediate-ring Pell rigidity uses its prescribed constant intersection
without assuming a constant-term retraction on that intermediate ring or
a square root in its coefficient field. The finite permutation proof gives
a positive Pell index at most m² for every positive modulus, including one.
The number-field ideal argument does not assume algebraic integrality,
and the Gaussian norm supplies an explicit positive integer multiple.
These incoming mappings concern the sibling report; they do not establish
the full-class universal quotient reviewed here.

The full two-thread Lean build passes 4,530 jobs, and the audit checks
15,849 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. No article or catalogue source changed during the merge,
so the validated 262-page and 33-page PDFs remain current. The index,
5,195 source references, 1,747 Markdown destinations and whitespace
checks pass.

## Representations, small quotients and finite-congruence closure

This pass reviews the sixteen standard results from `osq:cor:Oz` through
`osq:cor:dense`, including the previously reviewed localization consequence
`osq:cor:nofield`. The scope is the maintained text on representations,
residual targets, quotient reflection, small prime and principal ideals,
quotient size, and finite-congruence closure. Later prime examples,
completions, localizations, cardinal classifications and full reconciliation
of the parallel manuscripts remain pending. This is manuscript proof review,
not a new Lean proof or a certification of the full assembled report.

The original clause in `osq:prop:principal` that a nonconstant principal
quotient admits no set-sized quotient is false when read as excluding
further small images. The quotient Oz/(ω) surjects onto Z. The corrected
statement says that the quotient itself cannot be realized as a set-sized
ring; it also makes the later quantifier over arbitrary f explicit. The
universal set-sized image of A/(f) is D/(ct(f)), since ct(fA) = ct(f)D.
The examples ω, 2+ω and 1+ω distinguish a large quotient with infinite
small image, one with nonzero finite small image, and one with only the
zero small image. All three source quotients are nonzero. The notation
guide, ledger, catalogue and root README now preserve this distinction.

The Gaussian representation discussion records that the image of i need
not be central in the whole target. A new unnumbered consequence classifies
nonunital maps by pairs (e,j) with e²=e, ej=je=j and j²=−e, with the
multiplication identity supplied. The common-kernel proof uses specified
witnesses, class replacement and the empty-family case. The module proof
includes the zero vector space. The matrix proof spells out the passage
from a complex basis to a real basis and verifies both exhaustiveness and
uniqueness of the complex conjugacy list. The Gaussian automorphism proof
establishes invariance of the infinite-part ideal before descending.

The residual-target proof defines substitution on finite polynomials even
when the variables form a proper class. Quotient reflection now verifies
that ct(J) is a set ideal, the map on residues is well defined and surjective,
and the preimage identity holds in both directions. The ideal classification
proves uniqueness of its constant ideal. The small-prime proof distinguishes
the characteristic-zero image Z from its fraction field Q. The size argument
uses a set-indexed family and an explicit telescope contradiction. The
closure proof justifies preimages and intersections, including d=0. The
dense-principal consequence explains why even a nonunital small-target map
killing a unit-constant generator is zero.

Validation: three-pass builds produce a clean 263-page article and 33-page
catalogue, with no TeX warnings or box diagnostics. All 828 source labels,
1,656 auxiliary label numbers, 409 standard statements and nine principal
summaries are preserved; only the principal-quotient statement changes text.
The changed representation and principal-quotient pages were inspected
visually. All 4,626 indexed statements across 63 reports, 5,195 source-label
references, 1,747 local Markdown destinations across 226 files, and whitespace
checks pass. The unchanged source-06/source-11 finite verifiers retain their
previous 19,444-check baseline; they were not rerun and do not certify the
class-size or universal arguments. No Lean or shipped verifier source changed.

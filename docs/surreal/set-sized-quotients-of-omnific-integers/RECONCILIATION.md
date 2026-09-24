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

## Synchronization with the intersective-polynomial formalization

Merged `3b91351`, including `e684975` and `622f0fe`. The incoming statements
were compared with `odg:def:eq:Lambda`, `odg:def:prop:intersective` and its
following certificate caveat. They establish the expanded polynomial,
root exclusion in Q(i), intermediate Hahn rings and actual omnific rings,
roots modulo every positive integer, and the Gaussian multiple certificate.
The prime-two argument lifts x²+x−4 and transfers by 2x+1; it does not
assume that the derivative of x²−17 is invertible modulo two. The certificate
characterizes nonzero ordinary Gaussian constants, and cannot hold for an
actual Gaussian omnific element with zero constant term. These results do
not establish the full-class universal quotient theorem reviewed above.

The combined two-thread Lean build passes all 4,535 jobs. The audit checks
15,895 declarations and accepts only `propext`, `Classical.choice` and
`Quot.sound`. All 4,626 statement anchors across 63 reports, 5,196 source
references and 1,752 local Markdown destinations pass. The article and
catalogue sources and PDFs did not change during this merge; their clean
three-pass builds remain current. Whitespace checks pass.

## Prime quotients, completions, localizations and positive formulas

This pass reviews the seven standard results from `osq:cor:primeexample`
through `osq:prop:conservative`, plus the adjacent localization and
presentation examples. It completes the maintained Section 6 proof pass.
Later module and derivation results, cardinal classifications, and full
reconciliation of the parallel manuscripts remain pending.

The prime input for q = ω^(√2)+ω+1 was checked against Theorem B on page 3
of [L’Innocente–Mantova v5](https://arxiv.org/pdf/1710.07304v5).
The proof still imports primality; this review does not reprove the external
factorization theory. The quotient argument now proves characteristic zero
by degree and invokes the explicit large residue families for its size.
The adjacent continuum-family note has the same conditional consequence
once its referenced primality and nonassociation are supplied; its source
construction was not independently reviewed here. The unit-constant ideal
proof now separates its ring, module and proper-quotient assertions.

The completion proof specifies the divisibility index and all reduction
maps, proves compatibility with constant extraction, and identifies the
canonical coordinates and kernels. The Gaussian argument uses the cofinal
ordinary-modulus ideals and unique pairs of ordinary residues; multiplication
of compatible pairs gives the quadratic quotient ring without assuming that
it is a domain. A new unnumbered paragraph proves the topological
isomorphisms and density of the diagonal images using one common modulus.
Strong sums are compatible with the pulled-back topologies because only
finitely many summands contribute at exponent zero. The broader topology
classification is still imported from the cited sibling report; checking
its statement does not extend independent proof review to that theorem.

The monomial localization proof gives its embedding in the ambient field,
explains why shifting the lower support endpoint removes the coefficient
restriction, and exhibits an element whose inverse is missing. The
quotient-localization and presentation formulas now explicitly use Hom₁.
This removes a material ambiguity: if nonunital maps were allowed, the
zero map would contradict the empty-Hom assertion for a nonzero target.
The proof explains zero denominators, surjectivity on fractions of constants,
and the central inverse formula for noncommutative targets. Polynomial
presentations use finite evaluation and explicitly set-sized relation ideals.
The formula-conservativity proof gives the induction on equations,
conjunctions, disjunctions and existential witnesses. Its general
coefficient-ring and Gaussian variants are recorded as proof consequences;
the parameter and positivity restrictions are retained.

Validation: clean three-pass builds produce the 265-page article and
33-page catalogue, with no TeX warning or box diagnostic. Changed completion
and localization pages were inspected visually. All 828 source labels,
1,656 auxiliary label numbers, 409 standard results and nine principal
summaries are preserved. Four statements change only index or map-convention
text: completions, monomial localization, quotient-localization and
presentations. The 4,626-result index across 63 reports, 5,196 source-label
references, 1,752 local Markdown destinations across 226 files, and whitespace
checks pass. No Lean or shipped verifier code changed. Existing real omnific
completion mappings retain their scope; no Gaussian completion or new
formula-level mapping is asserted. The previous 4,535-job Lean build and
15,895-declaration axiom audit remain the documentation-only baseline.

## Small modules, derivations and the finite-side universal residue

This pass reviews the nine standard statements from `osq:thm:modules`
through `osq:lem:midempotent`, completing the maintained Sections 7–8 proof
pass. The subsequent support thresholds, cardinal classifications and full
parallel-source reconciliation remain pending. This is manuscript work;
no class universal-property theorem is newly formalized in Lean.

The module equivalence now verifies its inverse actions, both directions
of linearity, and preservation and reflection of exactness on the underlying
small groups. The nonsplitting argument identifies the additive/ring
section explicitly. The projectivity argument constructs a lift along a
surjection between small modules and explains why the class-sized source
of the constant-term map lies outside that test. A nonzero free class-ring
module contains the whole ring on one basis vector, so it cannot be small.

The derivation proof explains why additivity and Leibniz kill the integer
constants, gives the full Gaussian product calculation, and verifies
naturality. A Gaussian derivation is determined by m = ∂i with 2m=0;
M[2] is additive torsion, not M/2M. The F₂ example includes its coefficient
action i↦1 and ∂i=1. The square-zero-extension proof now checks its identity
and multiplication. The warning about coefficient linearity is supported by
a construction of a nonzero Q-derivation of R: differentiate one member of
a transcendence basis and extend over algebraic elements by the minimal-
polynomial formula. Polynomial representatives make the defining ideal
stable, and uniqueness makes the finite extensions agree. This uses choice
for a set basis and gives no continuous or canonical derivation.

The coefficient-weighted class derivations have an explicit support and
finite-coefficient proof of strong summability and Leibniz. Their independence
is proved by evaluating the finite linear combination at its distinguishing
monomials, and the complex extension is written down. The external
Berarducci–Mantova existence and normalization were checked against
[arXiv:1503.00315v3, page 2](https://arxiv.org/pdf/1503.00315v3), Theorem A
and the following normalization statement. They remain imported. The
bibliography now gives that version and the journal reference. The text
and notation guide distinguish preservation of infinitesimals, called a
small derivation in differential-field terminology, from a set-sized target.

The finite-side valuation lemma proves noncancellation of the denominator
and membership of the quotient in the infinitesimal ideal. The universal
proof uses an explicit Hartogs-indexed monomial family and a finite product
contradiction; it neither transports infinite sums nor assumes continuity.
The same argument also covers nonunital maps, as a new unnumbered consequence.
The finite-side corollary makes set-sized unital modules and unital ring maps
explicit. Its proof treats quotient kernels, module actions, derivations and
unit-forcing localizations individually. The idempotence proof includes zero
and both ideal inclusions, and supplies a single-product factorization.
The final residue incompatibility is multiplicative; the cited rotation-group
classification remains a comparison, not an imported step in this proof.

Validation: three clean passes produce a 266-page article and 33-page
catalogue, with no TeX warnings or box diagnostics. The derivation and
finite-side pages were inspected visually. All 828 labels, 1,656 auxiliary
numbers, 409 standard statements and nine principal summaries remain;
only `osq:cor:finitequotients` changes its statement text, to clarify the
size and unital conventions. The source-11 verifier passes all 1,858 exact
checks with its default seed and 80 cases, including all 16 Gaussian F₂
Leibniz cases. These are finite checks, not proofs of the class universal
property or Hahn summability. The 4,626-result index across 63 reports,
5,196 source-label references, 1,752 local Markdown destinations in 226 files,
and whitespace checks pass. No Lean or verifier source changed; the previous
4,535-job build and 15,895-declaration axiom audit remain the baseline.

## Synchronization with the three-equation definition of constants

Merged `f557bf6`, including `12956d3`. Compared the incoming declarations
with `odg:def:eq:system`, `odg:def:thm:constants` and its adjoining examples
and caveats. The predicate uses exactly five witnesses and three native
integer polynomials of degrees 3, 3 and 7. It defines the ordinary integer
and Gaussian constant rings in their actual omnific rings and in arbitrary
intermediate Hahn rings with the prescribed constant intersection. The
intermediate proof does not assume closure under constant extraction.
The converse supplies the stated bounded Pell index and bounded ordinary
residue witness. The examples check 1+i, exclude ω+i in the Gaussian
omnific ring, and prove the predicate holds everywhere in the full surreal
and surcomplex fields. These incoming results do not establish the small-
target module or residue universal properties reviewed in this pass.

The full two-thread combined build passes 4,547 jobs. Its transitive audit
accepts 15,954 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. The 4,626 anchors in 63 reports, 5,197 cited source labels,
1,758 local Markdown destinations and whitespace checks pass. The article
and catalogue sources and PDFs are unchanged by the merge, so their clean
three-pass builds remain current.

## Support thresholds and initial fixed-group bounds

This pass reviews the six standard results `osq:thm:support`,
`osq:prop:monomialbounds`, `osq:prop:fieldbound`, `osq:thm:criterion`,
`osq:thm:coinitial` and `osq:lem:cyclic`, with the adjacent threshold examples
and the support principal summary. The organizing theorem and the later
model classifications remain pending, as does full source reconciliation.

The finite-side extension criterion used an unqualified B^{<λ} as the
replacement for the positive-side at-most-μ ring. With λ=ℵ₀ this allows
extension to the original finite-support ring, which augmentation satisfies
without factoring through standard part. The corrected ring is B^{<μ⁺}
for infinite μ, so every permitted extension level includes countable
supports. The augmentation statement also specifies that each monomial must
belong to its domain: ω on the positive side and ω⁻¹ on the finite side.
The principal summary names ct and st on their respective sides. The
monomial-bound module clause explicitly assumes h>0 and an A-module.

The support proof treats zero separately, applies packing to a singleton,
and uses a Hartogs family without taking its sum. Each quotient separately
has support size at most max(original support size, ℵ₀); this estimate works
at singular uncountable bounds. The finite-side geometric product is formed
in the source, and only its finite identity is mapped. The alternate
small-field route was compared with `fkc:sb:lem:reservoir`: it uses rational
expressions in a set of tiny monomials, whose individual inverses have
countable supports. A scaled copy of the whole Hahn field need not satisfy
the support bound, since shifting does not reduce support cardinality.
The sibling report's later nonisomorphism classification remains an imported
comparison, not a newly reviewed conclusion here.

The finite-support augmentation proof handles coincident exponents and
cancellations by finite regrouping. The ordinary finite-quotient assertion
now identifies the kernels nZ+Π_fin explicitly. The bounded module and
derivation consequences explain the endomorphism-ring step and support-
preserving factorizations. This distinguishes equal finite quotient theories
from the stronger universal property for arbitrary set-sized targets.

The monomial-bound proof treats weighted equal-exponent differences,
nonunital maps on the positive ideal, negative-side division over arbitrary
coefficient fields, and the module collision individually. The field bound
writes its multiplier explicitly and bounds the module itself. Its general-
element conclusion retains the positive-monomial-divisor hypothesis; arbitrary
positive supports in a fixed group need not have a positive lower bound.
The two examples include attaining identity/regular representations and the
coefficient coding that gives continuum many series over a countable group.
The quantitative and coinitial criteria spell out unique factorization and
why singular cardinals cause no extra step. The cyclic-module lemma uses the
quotient ring A/Ann(m), counting it via the bijection with Am without claiming
that Am is itself a ring.

Validation: the article (267 pages) and catalogue (33 pages) build in three
clean passes, without TeX warnings or box diagnostics. The support and field-
bound pages were inspected visually. All 828 labels, 1,656 auxiliary numbers,
409 standard results and nine principal summaries remain. Only the support
summary, support theorem and monomial-bound statement change text, as
described above. All 4,626 indexed statements in 63 reports, 5,197 source
references, 1,758 local Markdown destinations across 226 files, and whitespace
checks pass. No Lean or verifier source changed. Existing finite checks were
not rerun to claim evidence for cardinal arguments; the previous 4,547-job
Lean build and 15,954-declaration audit remain the documentation-only baseline.

### Synchronization after the support review

Merged `31dacc2`, including `7aef1fc`, which formalizes the real quintic
integer definition and the four-square natural-number corollary. The source
comparison covers `odg:def:rem:quintic`, `odg:def:eq:quintic` and
`odg:def:cor:naturals`: the exact degree-five polynomial, ordinary witnesses,
ordered Hahn-ring and actual omnific instances, and the real/Gaussian
boundary examples. The Gaussian witness uses a complex square root of -i;
the ledger does not claim the particular trigonometric choice printed in
the article. The natural-number statement includes zero and allows the
four-square witnesses to range over the whole ordered ring. Neither the
quartic guards nor the support-threshold arguments are claimed as proved
by these additions.

Validation: `LEAN_NUM_THREADS=2 lake build` succeeds with 4,556 jobs. The
axiom audit covers 16,010 declarations and uses only `propext`,
`Classical.choice` and `Quot.sound`. All 4,626 indexed statements in 63
reports, 5,199 cited source labels and 1,766 local Markdown destinations
across 226 files pass their checks. The article and catalogue sources and
PDFs are unchanged by this merge, so their clean three-pass builds remain
current.

## Countable-support two-armed model

This pass reviews the six standard results `osq:lem:hcfield`,
`osq:lem:twosided`, `osq:lem:smallcommon`, `osq:lem:card03`,
`osq:thm:model03` and `osq:lem:cardinalfacts`, together with the adjacent
integer-part construction and continuum/power-set examples. It supplies
this model's contribution to the organizing theorem. The other four models,
the summary across all five models, later classifications and full
parallel-source reconciliation remain pending review.

The Gaussian alternative in the cardinal realization theorem printed the
real field as its fraction field. This is false: i belongs to the Gaussian
ring and its fraction field, but not to the real field. The corrected
statement explicitly pairs (A,F,D) with the real or complex construction.
The cardinality equality is unchanged, and the ledger records the original
error separately from the corrected statement's pending Lean status.

The field-closure proof puts finitely many supports inside their countable
subgroup, then uses a countable divisible hull for closedness. Real positive
square roots and odd-degree roots are separated from complex polynomial
roots; splitting real and imaginary parts proves both complexification
inclusions. The floor proof explains the endpoint correction when the
constant term is an integer and the remaining tail is negative. The scale
proof bounds coordinate indices, specifies both arms, and counts the final
forward tail. The common-divisor proof handles empty/zero families and
preserves support and coefficient constraints under translation.

The cardinality proof gives both upper bounds and injective coding by
countable subsets of a forward tail, verifies reverse well-ordering of the
coded supports, and shifts every smaller-scale field into the positive
ideal. The threshold proof is direct from the field bound, with an attaining
identity map and regular module, and an explicit factor through the constant
term. It therefore does not depend on a proof of the five-model summary.
For the fraction-field assertion, adjoining zero to the set to be bounded
ensures that the clearing exponent itself is positive.

The ideal proof exhibits a strictly increasing chain of principal ideals
of length cf(kappa), excludes every smaller generating family with a missing
half-scale monomial, and uses its set-indexed free modules to prove flatness.
Its product factorization gives idempotence and tensor vanishing against
constant-term modules. The constant quotient still fails flatness, witnessed
by tensoring the inclusion of a nonzero principal ideal. These are direct
proofs of the homological clauses used here; they do not review the entire
later homological package. The cardinal-arithmetic proof handles finite and
empty ranges and spells out the blockwise diagonal argument for cofinality.

Imported inputs were checked against
[L’Innocente–Mantova v5, Fact 2.1.1](https://arxiv.org/html/1710.07304v5#S2.SS1)
for closedness of full Hahn fields (translating the sign convention), and
[Stacks Lemma 10.39.3, Tag 05UT](https://stacks.math.columbia.edu/tag/05UT)
for directed colimits of flat modules. These remain imported results.

Validation: the article (268 pages) and catalogue (33 pages) build in three
clean passes with no TeX warnings or box diagnostics. The cardinal
realization and cardinal-arithmetic pages were inspected visually. All 828
labels, 1,656 auxiliary label/number pairs, 409 standard results and nine
principal summaries remain; the cardinal realization theorem is the only
changed statement. All 4,626 indexed statements in 63 reports, 5,199 cited
source labels and 1,766 local Markdown destinations across 226 files pass
checks, as does whitespace. No Lean or verifier source changed. Finite
verification programs were not rerun as evidence for the cardinal arguments;
the previous 4,556-job build and 16,010-declaration axiom audit remain the
Lean baseline for this documentation-only change.

### Synchronization after the countable-support model review

Merged `b22c26d`, including `b528168`, which adds the ordinary Pell growth
and parity lemmas and the six-witness real quartic definition. Compared
`odg:lem:pellsequence`, `odg:eq:pellmod8`, `odg:thm:standarddef`,
`odg:eq:standardsystem`, `odg:eq:standardquartic` and the subsequent vector
extension with the incoming declarations. The proof applies to the actual
omnific carrier, bounds each input and square witness by an ordinary Pell
coordinate, and proves all witnesses ordinary. The scalar polynomial has
exact total degree four; the vector formula keeps six witnesses for every
finite length, including zero. The distinct five-witness three-square guard
and source 07's alternative squared-coordinate quartic remain pending, as
the updated ledger states.

Validation: `LEAN_NUM_THREADS=2 lake build` passes with 4,560 jobs and an
axiom audit of 16,059 declarations, using only `propext`, `Classical.choice`
and `Quot.sound`. All 4,626 indexed statements in 63 reports, 5,202 source
references, 1,770 local Markdown destinations across 226 files and whitespace
checks pass. The merged changes do not touch the article or catalogue
sources/PDFs, preserving their clean three-pass builds. This synchronization
adds no Lean proof of the countable-support cardinal model reviewed above.

## Regular-cardinal two-armed model

Reviewed the five standard results `osq:lem:kappagap`,
`osq:prop:fieldclosure`, `osq:prop:kappachain`, `osq:lem:card06` and
`osq:thm:model06`, with the first-uncountable-cardinal example `osq:ex:CH`.
This supplies source 06's contribution to the five-model threshold summary;
the other three models, the full summary, later classifications and full
parallel-source reconciliation remain pending review.

Corrected a sign error in the discreteness proof: a nonzero series with a
positive leading exponent need not exceed every real constant, since -X^g
for g>0 is negative. The proof now specifies positive leading coefficient
and separates ordinary positive integers from positive infinite elements.
The field-closure proposition itself is unchanged.

The simultaneous-scale proof bounds the finite coordinate expressions and
handles zero and empty inputs. Field closure now uses one rational span of
the finitely many input supports, whose size stays below kappa using only
uncountability. The proof explicitly splits real/imaginary supports, identifies
the actual omnific intersection, clears denominators and verifies that the
floor remains within the support bound. Its hypotheses and sign convention
were compared with `fkc:lem:workspace`, `fkc:prop:closed` and
`fkc:rem:singular` in the first-kappa report. The imported closedness input
was checked against [Poonen, Corollary 4, page 10](https://math.mit.edu/~poonen/papers/amsval.pdf);
this is an input check, not a new proof of the full Hahn-field theorem.

An added unnumbered counterexample explains the regularity boundary.
At an uncountable singular kappa, the sum of X raised to the shrinking
exponents epsilon_(alpha_xi), along a cofinal sequence of length cf(kappa),
has support below kappa but no positive monomial divisor in the integer-part
ring. Every proposed positive divisor exponent eventually exceeds a support
exponent. Thus algebraic closure within the support bound does not imply
the gap property used in the threshold and generator proofs. No extension
of those theorems to singular kappa is claimed.

The principal-ideal chain proof gives its factors and strictness, explains
idempotence element by element, and excludes every smaller generating family
by a missing half-scale monomial. The cardinality proof separates finite and
infinite supports in the upper bound, codes functions by graphs to justify
the subset count, and checks reverse well-ordering of all coded lower-bound
supports. The smaller-scale field has exactly kappa^(<kappa) elements.
The threshold proof now derives the ring and module bounds directly from
it, supplies identity/regular-module attainment and the unique constant-term
factorization, and treats the Gaussian ideal and coefficients explicitly.
It does not rely on the unreviewed summary across all five models.

The continuum example now proves its cardinal arithmetic and constructs
the actual ordered-group reindexing between the two rational bases. This
induces the real and Gaussian ring isomorphisms at aleph_1 and commutes
with the constant term; it does not identify every embedded surreal element.
The root README, catalogue and notation guide distinguish ring size,
detection threshold, generator count, and per-element versus family support
bounds. All reviewed cardinal results remain pending in Lean.

Validation: the article (270 pages) and catalogue (33 pages) each build in
three clean passes, with no TeX warnings or box diagnostics. The field-closure,
singular-bound and continuum-example pages were inspected visually. All 828
labels, 1,656 auxiliary label/number pairs, 409 standard results and nine
principal summaries are preserved, and no numbered theorem statement changes.
All 4,626 statement anchors in 63 reports, 5,203 cited source labels, 1,770
local Markdown destinations across 226 files and whitespace checks pass.
No Lean or verifier source changed. Finite computations were not rerun to
claim evidence for these cardinal arguments; the previous 4,560-job Lean
build and 16,059-declaration axiom audit remain the documentation-only baseline.

### Synchronization after the regular-cardinal model review

Merged `d33b8cf`, including `601bf05`, which formalizes source 07's
alternative quartic `odg:def:eq:F4` and `odg:def:rem:quarticvariant`.
Compared its literal polynomial, exact degree four, six witnesses and
all-coordinate standardness with the manuscript. The intermediate Hahn-ring
proof needs precisely the integer constant intersection, without closure
under constant extraction, a square root of two in the coefficient field,
nontrivial exponents or an Archimedean coefficient field. The actual omnific
instance is proved separately. The printed Gaussian witnesses work for every
Gaussian omnific integer, and omega is proved to be an accepted nonconstant
element. The five-witness three-square guard remains pending; this merge
adds no proof of the cardinal models reviewed here.

Validation: `LEAN_NUM_THREADS=2 lake build` succeeds with 4,565 jobs and an
axiom audit of 16,094 declarations, using only `propext`, `Classical.choice`
and `Quot.sound`. All 4,626 statement anchors in 63 reports, 5,204 cited
source labels, 1,775 local Markdown destinations across 226 files and
whitespace checks pass. The merge leaves article and catalogue sources and
PDFs unchanged, so their clean three-pass builds remain current.

## Controlled fields and sharp models at every infinite cardinal

Reviewed the four standard results `osq:lem:gammabounds`,
`osq:lem:controlled`, `osq:lem:finitecoord` and `osq:thm:model08`, with
construction, embedding and residue-field consequences. The other two
models, the full organizing theorem, later classifications and full
parallel-source reconciliation remain pending review.

The construction now defines real closure as relative algebraic closure
inside the ordered countable-support Hahn field. Counting initial segments
of a countable reverse order type explains why each series adds at most
countably many truncations; arbitrary subseries are not adjoined. The proof
counts generators, rational expressions, algebraic roots and closure stages
separately. Real closedness of the union uses finitely many coefficients in
one stage. The real-closed Hahn-field input remains the imported
L’Innocente–Mantova Fact 2.1.1 checked in the earlier countable-support pass.

The finite-coordinate proof tracks rational expressions, truncations and
algebraic roots within the directed family of real closed fields H_E for
finite coordinate sets E. A nonzero polynomial uses only finitely many
coefficients, so one H_E suffices; its lack of proper ordered algebraic
extensions prevents a new coordinate from appearing. The added series
sum_(n<omega) X^(e_n) lies in the full countable-support field but is excluded
from the controlled field. This makes explicit that finite coordinate use
allows infinite supports but does not allow all countably supported series.
The actual surreal ring is now written with its image under Phi before
identifying the two carriers, and the ring's cardinal lower bound and floor
construction are stated separately.

The all-cardinal theorem now checks the quantitative criterion, unique
factorization through the constants, and quotient alternatives in both
cases. The alternatives can overlap at kappa=aleph_0, and include Z and
the zero ring. The generator proof includes countable cofinality and the
half-scale obstruction. The module proof uses a cyclic quotient ring,
without an endomorphism-cardinality assumption. Identity and regular-module
representations explicitly attain the threshold for each nonzero ideal
element.

The residue-field proof restricts nI=I to nonzero integers, exhibits 1/n in
the coefficient field, and notes the failure at n=0. It proves that every
positive-characteristic maximal ideal is pA. The characteristic-zero
construction applies the ordinary maximal-ideal theorem to the proper
ideal generated by 1+omega in a set-sized ring. Any nonzero integer in the
resulting maximal ideal would force omega and then 1 into it. A smaller
characteristic-zero residue field would be both an injective and a
surjective image of Z, which is impossible. The quotient sending the actual
omega to -1 and its obstruction to extension to the full omnific ring are
retained. No fraction-field equality with the ambient controlled field,
classification of residue-field isomorphism types, or exponential/derivation
closure is added.

Updated the root README, catalogue, notation guide and coverage ledger.
All four reviewed results remain pending in Lean. Validation: three clean
TeX passes each for the article (271 pages) and catalogue (33 pages), with
no warnings or box diagnostics; the finite-coordinate and residue-field
pages were inspected visually. All 828 labels, 1,656 auxiliary label/number
pairs, 409 standard results and nine principal summaries are preserved;
no numbered theorem statements change. All 4,626 statement anchors in 63
reports, 5,204 cited source labels, 1,775 local Markdown destinations across
226 files and whitespace checks pass. No Lean or verifier source changed.
Finite checks were not rerun as evidence for the cardinal construction;
the prior 4,565-job build and 16,094-declaration axiom audit remain the
Lean baseline for this documentation-only change.

## Synchronization after the controlled-field review

Merged the augmentation root-detector development through 88d9334,
including a2c9044, and checked its five new modules against
`odg:def:thm:augdetector`, `odg:def:eq:augdetector`,
`odg:def:eq:witness`, `odg:def:thm:detector` and
`odg:def:eq:detector`. The generic theorem uses the full coefficient
pullback, an ordinary polynomial without ordinary roots, a coefficient-field
root, and divisibility of an ordinary value by each nonzero ordinary scalar.
The explicit affine witnesses require no domain or reducedness assumption
on the ambient algebra. The product example verifies the printed certificate
for a zero divisor in the first-projection pullback Z times R.

The Lambda specialization proves the literal two-witness detector in the
full integer and Gaussian Hahn pullbacks and, separately, on the actual
omnific carriers. These claims do not extend to arbitrary intermediate
rings. Precise support bounds, degree formulas and remaining printed
certificates are still pending. The README and implementation mappings
accurately distinguish these scopes.

Validation: the two-thread full Lean build passes all 4,570 jobs; its audit
checks 16,126 declarations using only propext, Classical.choice and
Quot.sound. All 4,626 statement anchors across 63 reports, 5,207 cited
source labels, and 1,780 local Markdown destinations across 226 files pass.
The merge changes no TeX sources or PDFs, so the clean three-pass builds
recorded above remain current. Whitespace checks pass.

## Synchronization of ideal tests and the constant-term graph

Merged cf9bcce and 4b62e90 and reviewed all six new modules against
`odg:def:thm:idealtest`, `odg:def:eq:idealtest`,
`odg:def:cor:universal`, `odg:def:thm:ctgraph` and
`odg:def:eq:ctgraph`. The ideal test first proves the value-membership
criterion without forming a quotient, then handles native ideal quotients,
including the top ideal and zero ring. The greatest-ideal result includes
membership of the kernel itself. Negating the detector gives the universal
kernel and equal-constant formulas. Instances cover the full real and
Gaussian Hahn pullbacks and separately the actual omnific carriers.

The graph proof combines the ordinary-constant predicate with the quadratic
kernel test, expands exactly six existential witnesses, and proves existence
and uniqueness of the output, not of those witnesses. The Hahn versions
allow arbitrary ordered abelian exponent groups; their general coefficient
fields have characteristic zero and a square root of two. The actual real
version also admits any predicate defining exactly the integer constants.
The ledger correctly leaves the single-polynomial degree-ten variant,
quartic-graph and canonical-splitting corollaries outside this mapping, and
does not claim the external intersection-of-integer-multiples discussion.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,576 jobs and audits
16,185 declarations with only propext, Classical.choice and Quot.sound.
All 4,626 statement anchors across 63 reports, 5,209 source-label references,
and 1,786 local Markdown destinations across 226 files pass. Whitespace
checks pass. No TeX or PDF changes were merged; the article and catalogue
builds from the controlled-field review remain current.

## Countable-support one-arm models and residue fields

Reviewed the four standard results `osq:lem:tail`, `osq:thm:barrier`,
`osq:lem:coefffield` and `osq:thm:residue`, together with construction,
embeddings, exact generator count and the support-bound counterexample
`osq:rem:fstar`. The source-11 model, full organizing theorem, later
classifications and full parallel-source reconciliation remain pending.

Corrected the maintained claim that lambda^aleph_0=lambda automatically
implies the continuum lower bound: 0 and 1 satisfy the equality too.
Infinitude is now explicit in the construction, principal summary,
organizing table and realized-cardinal comparison. Source 09's original
stronger continuum lower bound was already sufficient. The ledger records
the missing hypothesis and keeps all four reviewed results pending in Lean.

The tail proof bounds the countable set of first coordinates in omega_1,
then checks every finite multiple of a later basis vector. Only regularity
of omega_1 is used. Cardinality bounds separately count the rational
exponent group, supports and coefficients, and positive monomials give the
lower bound for the ideal, ring and field. The ordered embedding uses
ordinal multiplication/addition and distinguishes exponent coordinates
from actual monomials; the image of the first basis monomial is omega.
The real integer-part assertion uses the previously checked truncation
and endpoint rule. The countable-support field-closure input is the
already reviewed lemma, with no new external closedness input.

The barrier proof displays the two injections and transports only finite
product identities. It also handles nonunital maps and noncommutative
targets. Quotient alternatives include the zero ring and the integer
quotient, and the continuum example excludes all countable detecting
targets without CH. Coefficient-field recovery now verifies the ratio's
additivity, multiplication, restriction to D, independence of the detected
element and uniqueness relative to the given map.

The residue-field proof makes the proper-ideal and maximal-ideal steps
explicit, identifies the positive-characteristic arithmetic ideals, checks
the reverse-well-ordered support and cancellation in the comaximality
identity, and explains the set-indexed maximal-ideal choices. Residue
fields attain the exact field and module thresholds. Separate arguments
prove that the finite residual is the nonzero purely infinite ideal while
the Jacobson radical is zero. The increasing principal-ideal chain and
countable-support-union obstruction give exactly aleph_1 generators.
The unrestricted-support example explicitly produces a negative exponent
in every proposed positive-monomial quotient. No classification of the
unrestricted ring or of residue-field isomorphism types is added.

Updated the root README, report guide, catalogue, notation guide and
coverage ledger. Validation: three clean TeX passes for the article
(273 pages) and catalogue (33 pages), no warnings or box diagnostics;
the coefficient-field and residue-field pages were inspected visually.
All 828 source labels, 1,656 auxiliary label/number pairs, 409 standard
results and nine principal summaries are preserved. Only the principal
summary osq:main:thresholds changes among those numbered statements.
All 4,626 statement anchors across 63 reports, 5,211 cited source labels,
and 1,786 local Markdown destinations across 226 files pass, as does
whitespace validation. No Lean or finite verifier source changed; finite
checks were not rerun as evidence for cardinal arithmetic or maximal-ideal
existence. The prior two-thread 4,576-job build and 16,185-declaration
axiom audit remain the Lean baseline for this documentation-only pass.

## Synchronization of definable splittings and quantified graphs

Merged 5a013b3, including 47e4d2b, after the source-09 review. Checked all
four new Lean modules against `odg:def:cor:splitting`, its multiplication
formula, and `odg:def:rem:sigma2`. The splitting package proves the
section/retraction identity, injective kernel inclusion, native exactness,
surjectivity, and literal existential formulas for kernel, retraction and
section. Its additive equivalence retains the actual kernel subtype;
the multiplication identity retains both cross terms and the kernel
product. No direct-product ring assertion is introduced.

Both printed quantifier orders expand the five-witness Xi system and the
universal Lambda inequality. Specializing the universal variables to zero
extracts the fixed ordinary-constant witness in the universal/existential
form. The detector and quadratic kernel formula identify these with the
six-witness existential graph. Full real and Gaussian Hahn pullbacks and
actual omnific carriers are instantiated separately. The general splitting
also covers the characteristic-zero coefficient fields containing a square
root of two from the preceding graph theorem. No quantifier optimality or
witness uniqueness is claimed. README and ledger scopes match the proofs;
the separate degree-ten and quartic graph variants remain pending.

Validation: the two-thread full Lean build passes all 4,580 jobs, and the
axiom audit checks 16,230 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,212 source-label references, and 1,792 local Markdown
destinations across 226 files pass. Whitespace checks pass. The merge
changes no TeX sources or PDFs, so the clean article and catalogue builds
from the source-09 review remain current.

## Source-11 support models and the organizing threshold theorem

Reviewed `osq:prop:lex`, `osq:prop:card11` and
`osq:thm:thresholds`, together with `osq:rem:reconcile` and the
source-11 generator calculation. This completes the manuscript pass over
all five model constructions and their organizing ring/module theorem.
The full homological package, including the Ext clause of the principal
summary, later classifications and full parallel-source reconciliation
remain pending review. All three reviewed results remain pending in Lean.

The source-11 proof now counts the rational group and proves both
coinitiality inequalities. It checks field closure inside the full Hahn
field over the subgroup generated by finitely many small supports; only
uncountability is needed at this step. A final basis tail encodes every
subset of size less than kappa, with distinct coefficient-one series even
in positive characteristic. The upper bound separately counts finite and
infinite supports and their coefficient assignments. Scaling the smaller-
scale field into the ideal gives equal cardinalities for that field, ideal,
ring and ambient field. The gap, field bound, identity map and regular
module then prove the exact threshold without using the organizing theorem.

The strictly increasing principal-ideal chain proves idempotence and gives
kappa generators. Regularity bounds the union of fewer than kappa supports;
a common monomial divisor and the missing half-exponent monomial rule out
any smaller generating family. This use of regularity is distinguished
from field closure. No coefficient characteristic assumption is added.

Corrected the introduction's claim that all coefficient choices are
omnific subrings: source 11 permits D=K=F_p, so there is no unital embedding
into a characteristic-zero omnific ring. The title now says set-sized
rings, and the embedding claim is restricted to the displayed real/integer
and Gaussian cases. The ledger records this scope correction. The notation
guide keeps the regular uncountable one-arm group and coefficient data
explicit.

The organizing proof now checks the ambient and smaller-scale fields in
all five models before applying the gap argument. It includes nonunital
maps, noncommutative targets, module orbit bounds, attainment for each
nonzero ideal element, unique constant-term factorization and both quotient
cases, including the zero ring. The comparison uses theta for realized
size, proves that (kappa^{<kappa})^aleph_0=kappa^{<kappa} for regular
uncountable kappa by bounding the lengths in a countable sequence, and thus
justifies source 08's exceptional realized sizes even when source 11 has
smaller coefficient fields. It keeps generator counts and fraction-field
claims separate from size and detection thresholds.

Updated the root README, report guide, catalogue, notation and coverage
ledger. Validation: three clean TeX passes for the article (275 pages)
and catalogue (33 pages), with no warnings or box diagnostics; the table
and generator/threshold pages were inspected visually. All 828 labels,
1,656 auxiliary label/number pairs, 409 standard results and nine principal
summaries are preserved, with no numbered theorem statement changes.
All 4,626 anchors across 63 reports, 5,212 source-label references and
1,792 local Markdown destinations across 226 files pass, as does
whitespace validation. No Lean or finite verifier source changed; finite
checks were not rerun as evidence for cardinal bounds. The prior
two-thread 4,580-job build and 16,230-declaration audit remain the Lean
baseline for this documentation-only pass.

## Synchronization of constant-term homomorphism proofs

Merged c990b63, including 4ee4707, and checked its three new modules
against `odg:def:thm:homct`. Mapping the existential graph witnesses
proves commutation with embedded constant terms. Integer homomorphism
uniqueness fixes the integer constants; quadratic-ring extensionality and
the two square roots in a domain give the Gaussian identity/conjugation
alternative. The sign of the image of i and a single action valid for
every input occur together in each branch.

The Hahn theorem allows different ordered abelian exponent groups and
different characteristic-zero coefficient fields containing a square root
of two, with injective Gaussian coefficient embeddings where needed.
Actual omnific and Gaussian omnific instances allow different universes.
No target-size bound, continuity or pointwise fixation of all ambient
coefficients is assumed. The proof preserves equations and existential
witnesses; it neither assumes preservation of arbitrary first-order
formulas nor claims annihilation of the purely infinite ideal. The README
and ledger accurately reflect this scope.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,583 jobs and the
axiom audit checks 16,239 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,212 source-label references and 1,795 local Markdown
destinations across 226 files pass. Whitespace checks pass. No TeX
sources or PDFs changed in the merge; the 275-page article and 33-page
catalogue builds from this review remain current.

## Set-sized homological package and coefficient-module thresholds

Reviewed `osq:lem:projideal`, all seven clauses of
`osq:thm:homological`, and `osq:thm:extthreshold`, including the Ext
clause of the principal threshold summary. The decomposition A=D⊕I is
explicitly additive. The constant inclusion is a ring and D-linear
section, whereas the quotient sequence does not split as A-modules.
Making this category explicit is the only numbered-statement change.

The projective-ideal argument constructs a finite generating family from
a split free module. The homological proof now details the filtered union
of principal ideals, tensor balancing, flat-resolution Tor computation,
nonflatness witness, projective base change and tensor–Hom adjunction.
Comparison maps identify the canonical inflation map and its inverse
without assuming that D is flat over A. Schanuel's lemma and the explicit
Yoneda splice justify the projective-dimension bound and Ext nonvanishing.
The flat-colimit, projective-module and resolution inputs were checked
against the Stacks Project, Tags 05UT, 05CF and 00O3 and Section 15.60.

An explicit countable telescope proves pd_A D=2 when I is countably
generated; the general conclusion remains only pd_A D≥2. Finite-support
cardinal counting in a free presentation gives a degree-two coefficient
module of size exactly |A|. The thresholds measure the carrier of the
coefficient module, not the Ext group. For all five models, A/xA has size
|A| when x is nonzero in I: a trivial I-action would force I=xA,
contradicting nonfinite generation.

Updated the root README, report guide, catalogue, notation and coverage
ledger. All three reviewed results remain Pending in Lean; later
core/tensor results and full parallel-source reconciliation remain pending
review. Validation: three clean TeX passes for the article (278 pages)
and catalogue (34 pages), with no warnings or box diagnostics; the Ext
comparison and telescope pages were inspected visually. All 828 labels,
1,656 auxiliary label/number pairs, 409 standard results and nine principal
summaries are preserved. All 4,626 statement anchors across 63 reports,
5,212 source-label references and 1,795 local Markdown destinations across
226 files pass, as does whitespace validation. No Lean or finite-verifier
source changed. The previous two-thread 4,583-job build and
16,239-declaration axiom audit remain the Lean baseline for this
documentation-only pass.

## Synchronization of detector counterexamples and their Hahn realizations

Merged f48869d, including 1714764 and 2113ae6, and checked the four new
modules against `odg:def:rem:rootneeded`. Polynomial Pell rigidity uses
an algebraic closure, constant polynomial units and descent of degree.
For Z+X Q[X], evaluation at minus one is surjective with kernel (1+X),
so the quotient is Q and the detector rejects an element with constant
term one. The ordinary-integer predicate Xi still defines the integers.
For Z[X], evaluation at minus one rules out a detector certificate even
when the ambient real coefficient field contains a root of Lambda.
The polynomial X/2 witnesses strict containment in the full pullback.

Negative Hahn order proves faithful polynomial evaluation. The new
bridge realizes both examples at single(-1,1) in the integer-exponent
Hahn workspace, verifies the quotient and constant intersection, and
transfers the detector obstruction and integer definition. The README
and ledger keep these set-sized workspace realizations distinct from the
class of all surreals; the hypotheses on full pullbacks and coefficient
roots remain explicit.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,587 jobs. The
axiom audit checks 16,337 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,213 source-label references and 1,799 local Markdown
destinations across 226 files pass, as does whitespace validation.
No TeX source changed in this merge, so the reviewed 278-page article
and 34-page catalogue remain current.

## Finite-support cores, face resolutions and exact flat dimensions

Reviewed eight results in dependency order: `osq:hd:lem:cores`,
`osq:hd:prop:finite`, `osq:hd:lem:faces`, `osq:hd:thm:resolution`,
`osq:hd:cor:arithmeticTor`, `osq:hd:prop:etale`,
`osq:hd:thm:boolean` and `osq:hd:cor:fd`. All numbered statements
are unchanged. Later coefficient-lattice, tensor and derived results,
and full parallel-source reconciliation, remain pending review.

The domain proof identifies finite polynomial subalgebras explicitly;
the normal-form embeddings keep coefficient fields, coordinate rank and
Archimedean scales distinct. The finite-target proof treats the zero ring
and noncommutative targets, writes the module annihilation calculation,
and identifies compatible quotient systems and the p-adic kernel.
The coefficient-sum augmentation is distinguished from constant extraction.
The root README restricts the finite-quotient comparison to the integer
and Gaussian cases of the stated proposition.

The face-ideal proof uses strict coordinate subtraction to keep arbitrary
K coefficients in the tail, handles the zero element, and gives explicit
bounds contradicting finite generation. The resolution has a written
simplex contraction in each exponent degree. This proves exactness with
finite-support preimages even in countable rank, without claiming an
A-linear splitting. After tensoring, the quotient complex is computed
anew. Its four exponent cases exhibit the signed contraction, the isolated
higher faces, and the singleton map K to K/D whose kernel is D. The
quotient K/D is an additive D-module, not a ring quotient. Truncation and
dimension shifting give the two exact flat dimensions and their infinite-
rank limits, consistently with vanishing positive self-Tor.

The formal lifting proof includes existence, uniqueness and reduction of
the lift for every nilpotent test ideal. Nonflatness and failure of finite
presentation have separate elementary proofs. The derivation argument
explains the universal differential conclusion and distinguishes the
section D to A from the formally etale map A to D. The standard inputs
were checked against the Stacks Project, Tags 05UT and 060H and
Section 10.6; the finite-presentation argument is also written directly.

Updated the root README, report guide, catalogue, notation and ledger.
All eight results remain Pending in Lean. Validation: three clean TeX
passes for the article (280 pages) and catalogue (34 pages), no warnings
or box diagnostics, and visual inspection of the resolution and Boolean
Tor pages. All 828 labels, 1,656 auxiliary label/number pairs, 409 standard
results and nine principal summaries are preserved. The existing exact
finite audit passes all 780 multidegrees in ranks one through four, with
F the full coordinate set and coefficient pair Q inside Q(sqrt(2)); this
is supporting evidence for those cases, not general proof or Lean coverage.
All 4,626 statement anchors across 63 reports, 5,213 source-label references
and 1,799 local Markdown destinations across 226 files pass. Whitespace
validation passes. No Lean or verifier source changed; the previous
two-thread 4,587-job build and 16,337-declaration axiom audit remain the
Lean baseline for this documentation-only pass.

## Synchronization of the detector witness support and degree proofs

Merged 6d969c5, including a1efe7f, and checked its three new modules
against `odg:def:prop:support` and the preceding explicit formulas.
Native coefficient-field polynomials produce t of degree one and s of
degree five, with the factored expression and detector equation proved.
Root exclusion makes the affine slope nonzero. Augmentation supplies the
ordinary constant coefficients needed for membership in the full pullback.
The Hahn support bound uses finite unions of repeated pointwise sumsets,
including the zeroth sumset {0}; the existing polynomial-degree theorem
gives exact omega-degrees for nonconstant input. Both real and Gaussian
Hahn instances include equation, membership, supports and degrees together.
The ledger correctly leaves actual-carrier transport Pending and adds no
rank, divisibility or support-cardinality assumption.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,590 jobs, and the
axiom audit passes for 16,382 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,213 source-label references and 1,802 local Markdown
destinations across 226 files pass. Whitespace checks pass. The merge
changes no TeX source; this review's clean 280-page article and 34-page
catalogue builds remain current.

## Lattice presentations, dimension bounds and the coherence hypothesis

Reviewed `osq:tn:thm:syzygy`, `osq:tn:prop:nonflat`,
`osq:hd:thm:fdlattice`, `osq:hd:prop:pd`,
`osq:hd:thm:orderedcone` and `osq:hd:thm:collapse`, with their
immediate comparisons. Setting (L) now explicitly takes a nonzero lattice
of rank at least one. The presentation proof constructs the kernel,
proves the minimal generator count by passage to Frac(D), and explains
why the module nevertheless has rank one over Frac(A). It distinguishes
the displayed class kernel from the later theorem about all presentations.

The auxiliary tensor carrier has its coupled A-action checked explicitly.
The antisymmetric element is nonzero even in characteristic two, and its
image in the ideal tensor square gives the multiplication-kernel
obstruction to flatness. For flat dimension one, this yields an explicit
nonzero self-Tor witness for the cyclic quotient. Dimension shifting,
the quadratic coefficient calculation, telescope exactness, the
Archimedean coinitiality of 2^(-n)g, and the projective-dimension bounds
are expanded. The condition c² in D is used for the explicit quadratic
self-Tor formula, not for the dimension bounds. The ideal H=(X^g,cX^g)A
is written uniformly in both types of cone.

Corrected the unconditional noncoherence clause in the ordered-cone
theorem: the given certificate requires K not equal to Frac(D). For
D=K and Gamma=Q, any finite family lies in K[X^(1/n)]. A polynomial
greatest common divisor and Bezout identity show that its extended ideal
is principal, so every finitely generated ideal of K[Q_nonnegative] is
finitely presented and the ring is coherent. The manuscript includes
this counterexample; the integer/real and Gaussian/complex cases still
meet the repaired hypothesis. No complete coherence classification is
claimed. The same theorem now states gamma>0 for its monomial Tor
witness. The ledger flags the original statement Needs correction and
keeps the corrected results Pending in Lean. The only other changed
numbered statement standardizes H in the lattice-dimension theorem.

The cone-enlargement proof distinguishes quotient base change, which
needs no flatness, from preservation of ideal intersections, which does.
The reconciliation no longer suggests that these embeddings compute the
class ring's dimensions; its separate two-universe flatness statement
has separate input. Later tensor normal forms, sharp derived dimensions
and full parallel-source reconciliation remain pending review.

Updated the root README, report guide, catalogue, notation and ledger.
Validation: three clean TeX passes for the 283-page article and 34-page
catalogue, no warnings or box diagnostics; dimension and correction pages
were inspected visually, and the ordered-cone theorem is kept together.
All 828 labels, 1,656 auxiliary label/number pairs, 409 standard results
and nine principal summaries retain their numbering. The existing tensor
verifier passes 2,189 exact assertions, including 120 finite-support
action/balancing cases. Its additional checks of later formulas do not
extend the manuscript review scope or provide Lean coverage. All 4,626
anchors across 63 reports, 5,213 source-label references and 1,802 local
Markdown destinations across 226 files pass, as does whitespace validation.
The standard coherence and Schanuel inputs were checked against Stacks
Tags 05CU and 00O3. No Lean or verifier source changed; the two-thread
4,590-job build and 16,382-declaration audit remain the baseline for this
documentation-only pass.

## Tensor normal forms and universal properties through symmetric powers

Reviewed `osq:tn:lem:absorption`, `osq:tn:thm:tensor`,
`osq:tn:prop:higher` and `osq:tn:thm:powers`. All numbered
statements are unchanged. The algebraic interface in the introduction is
restricted to this tensor/power subsection; later homomorphism and other
classifications are not claimed to follow from that interface alone.
Products of lattices are explicitly D-spans of products and are nonzero
finite free D-modules under the stated principal-ideal hypothesis.

Absorption specifies which scalars lie in A and can be moved between
factors, constructs the inverse, and proves the factorization and
uniqueness for a fixed class-valued balanced map. The two-factor normal
form now checks both compositions and gives a separate class carrier
proof: H(u,t)=j_b(u)+s_b(t), with h s_b(t)=j_b(h m(t)) verifying the
cross term required for A-linearity. The constant map is only D-linear
on its own. Finite expressions force uniqueness, without a collection
of all class modules or a quotient of a proper class.

The multiplication kernel is identified with all A-torsion; the proof
includes its exact annihilator when nonzero, its D-freeness and rank,
and the zero-kernel exception. The quadratic example writes the two
basis vectors and solves their coefficient equations. The higher-factor
proof constructs the multilinear map and inverse and reduces every
term containing a tail to its product, keeping all balancing scalars
inside A. It verifies the permutation action and the empty-family
convention separately.

Exterior powers use constant extraction as an alternating universal map;
tail terms vanish, the action factors through ct, and the exceptional
first degree is explicit. For symmetric powers the entire relation
module is zero in the tail coordinate and the ordinary permutation
relation module in the constant coordinate. Only that finite free
D-module is quotiented in the class construction. Rank and torsion
calculations include the boundary cases. The exterior example is
clarified as a family of ideals with arbitrarily large nonvanishing
degree; each finite-rank member has vanishing powers above its rank.

Updated the root README, report guide, catalogue, notation and ledger.
All four results remain Pending in Lean. Rees equations, later Hom and
derived classifications and full source reconciliation remain pending
review. Validation: three clean TeX passes for the article (286 pages)
and catalogue (34 pages), no warnings or box diagnostics, and visual
inspection of the class universal-property and power pages. All 828
labels, 1,656 auxiliary label/number pairs, 409 standard results and nine
principal summaries retain their statements and numbering. All 4,626
anchors across 63 reports, 5,213 source-label references and 1,802 local
Markdown destinations across 226 files pass, as does whitespace checking.
Standard tensor/exterior/symmetric constructions were checked against
Stacks Section 10.13, Tag 00DM. The existing tensor verifier's unchanged
formulas retain the previous 2,189-assertion run as finite supporting
evidence; it was not rerun as a test of class universal properties.
No Lean or verifier source changed, so the previous two-thread 4,590-job
build and 16,382-declaration audit remain the Lean baseline for this pass.

## Synchronization of witness bounds on the actual omnific carriers

Merged 66b7995, including c75088f and fc761f4, and checked the two new
modules against `odg:def:prop:support`. The witnesses are evaluated
inside the actual real and complex support rings. Canonical normal-form
maps are proved injective and compatible with constants and constant
extraction. Support reindexing commutes with finite sumsets, and the
Hahn order in the dual exponent order gives the actual leading exponent.
The transport proves the equation, both support bounds and exact degree
identities together. Nonconstant inputs and both witnesses are proved
nonzero; the surcomplex version also identifies the native degree with
minus infinity at zero. The actual omnific and Gaussian omnific witnesses
have their ordinary constant coefficients proved. No surjectivity onto
an entire Hahn carrier is used or claimed. The updated README and ledger
correctly record completion of the actual-carrier support/degree clause.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,592 jobs; the
axiom audit checks 16,445 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,213 source-label references and 1,804 local Markdown
destinations across 226 files pass, as does whitespace validation.
No TeX source changed in the merge, so this review's clean 286-page
article and 34-page catalogue remain current.

## Rees presentations, first nonlinear degree and the every-degree family

Reviewed `osq:tn:thm:rees`, `osq:tn:thm:degree` and
`osq:tn:cor:alldegrees`, together with the product/scaling setup and
immediate examples. All three numbered statements are unchanged.

The Rees setup distinguishes the formal grading variable from the
monomial used to scale a coefficient-lattice module into an ideal.
The product law is proved by finite sums and a fixed nonzero lattice
coefficient. The symmetric-algebra proof supplies a graded carrier,
its multiplication and a finite reduction of every tail monomial by
the linear relations. This proves the presentation and constant-polynomial
injection explicitly, including the interpretation for class rings.
The arithmetic kernel is identified degree by degree and shown to be
all A-torsion, with its action factoring through constant extraction.

Clarified that the nonlinear kernel is finitely generated as an ideal
of the symmetric algebra. If nonzero, it is not finitely generated as
an A-module: multiplying one nonzero homogeneous relation by arbitrary
powers of a presentation variable gives unbounded degrees. This resolves
the ambiguous comparison with the infinitely generated linear relation
module, without changing a numbered assertion.

The algebraic-degree proof treats nonmonic primitive polynomials,
explains dehomogenization and Gauss divisibility, and homogenizes without
localizing the polynomial ring. The constant-polynomial injection proves
that the degree-d relation survives the linear quotient. The every-degree
family uses Eisenstein irreducibility and equality of integer lattices,
then derives the generator and kernel counts with their boundary cases.
The added example alpha = sqrt(2)/2 shows explicitly that bounded ranks
do not force the increasing power lattices to stabilize.

Updated the root README, report guide, catalogue, shared notation and
coverage ledger. These three results remain Pending in Lean; later Hom
and derived classifications and full source reconciliation remain pending
review. Standard symmetric and Rees constructions were checked against
Stacks Tags 00DM and 052P. The existing finite tensor verifier's previous
2,189-assertion run remains supporting evidence for its unchanged formulas;
it was not rerun as a test of the new class-carrier arguments.

Validation: three clean TeX passes for the article (287 pages) and
catalogue (34 pages), with no warnings or box diagnostics; visual review
of the presentation, homogenization, every-degree and catalogue pages.
All 828 source labels, 1,656 auxiliary label/number pairs, 409 standard
results and nine principal summaries retain their statements and
numbering. All 4,626 statement anchors across 63 reports, 5,214 source-label
references and 1,807 local Markdown destinations across 226 files pass,
as does whitespace checking.

## Synchronization of printed detector certificates

Fast-forwarded b2cd705 to 0e4e94c, including 81c55c1, before the Rees
review. Checked the three new modules against `odg:def:ex:certificates`
and the preceding nonunit example. The generic polynomial identities
and their augmentations instantiate on the actual omnific carrier:
the printed witnesses for 1+x and 2+x have the stated constant
coefficients, and nonzero purely infinite x makes 1+x a nonunit.
The reciprocal-exponent example is constructed by its canonical normal
form, with coefficient one at each positive reciprocal natural exponent,
small reverse-well-ordered infinite support, and zero constant term.
It is rejected by the detector. The ledger correctly distinguishes this
normal-form construction from a separate analytic convergence theorem.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,595 jobs. The
axiom audit checks 16,507 declarations using only propext,
Classical.choice and Quot.sound. No TeX source changed in that merge.

## Synchronization of the degree-ten constant-term polynomial

Merged 88f1cd1 and checked its three new modules against the unnumbered
single-polynomial variant following `odg:def:thm:ctgraph`. A faithful
ordered-ring inclusion separates the two squared equations. The resulting
formula combines the quintic definition of ordinary integer constants
with the quadratic test for the constant-term kernel, giving exactly the
constant-term graph with eight witnesses. Native integer multivariate
polynomials encode the expression and its evaluation; a variable
retraction preserves the quintic's degree, so its square has degree ten
and cannot cancel with the added term of degree at most four.
The specialization covers both the actual real omnific carrier and the
full ordered Hahn pullbacks with a coefficient square root of two.
The ledger makes no Gaussian single-polynomial or degree-optimality claim;
the separate quartic graph remains pending.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,598 jobs; the
axiom audit checks 16,534 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across 63
reports, 5,214 source-label references and 1,810 local Markdown
destinations across 226 files pass, as does whitespace checking.
The merge changes no TeX source, so the three-pass 287-page article and
34-page catalogue from the Rees review remain current.

## Scalar Hom, ideal classes, duals and common-scale matrices

Reviewed `osq:tn:thm:hom`, `osq:tn:thm:pic`, `osq:tn:thm:duals`
and `osq:tn:thm:matrix`, the arithmetic supporting
`osq:tn:ex:sqrt10`, and the following Gaussian-scope paragraph.
The four theorem statements and the example statement are unchanged.

The Hom proof clears two denominators at a time to show that every map
between nonzero submodules of the fraction field is multiplication by
one scalar. This covers the infinite tail and coefficient ring as well
as lattice modules. For the class case it gives an explicit scalar
carrier for Hom. Expanding constants and tails proves the colon formula;
units of B give the isomorphism and automorphism criteria. The multiplier
ring is embedded in a finite lattice to prove freeness, and its faithful
matrix action gives integrality. A real cubic example explains the
qualification that its number field need not be totally real.

The ideal-class setup specifies the real base and the full rank of a
fractional ideal. Torsion-free tensor multiplication is realized by its
image L(PQ), also for class carriers. The proof checks independence of
representatives, identity and inverses, and excludes invertibility over A
using the nonflatness obstruction. The subsequent identity discussion
now retains the necessary number-field-degree-at-least-two condition;
when the field is Q, the identity is A. The quadratic example's product,
explicit inverse, determinant index and modulo-five obstruction are
spelled out. No Gaussian preservation of this nontrivial real ideal class
is inferred from the general Gaussian version.

The dual proof first obtains a shifted allowed normal form from qX in A;
this also forces finite rational support in the set-sized model.
Testing negative exponents and ordinary constants proves the two colon
identities in both real and Gaussian cases. Evaluation gives the actual
bidual inclusion, and the ordinary additive quotient k/M realizes the
class quotient. Scaling and the rank-one exception are explicit.

The matrix proof supplies saturation over the PID, the resulting direct
summand, a finite-coordinate kernel isomorphism and its inverse criterion.
Schanuel's finite-free pullback excludes any finite presentation when the
kernel has a tail summand. When the ordinary kernel is rational, the
remaining columns form a free image basis. Clearing denominators proves
the rationality equivalence; zero matrices and zero kernels are included.
The Gaussian paragraph now states the support and unit hypotheses used,
and proves equality of real algebraic degrees after adjoining i.

Updated the root README, report guide, catalogue, shared notation and
ledger; the four theorems remain Pending in Lean. Later relation/moduli
and derived classifications and full source reconciliation await review.
Added primary references to Stacks Tags 0AFW and 0517 for invertibility
and presentation independence. The existing tensor verifier's previous
2,189-assertion run covers unchanged finite formulas, including the
quadratic ideal product; it was not rerun or treated as verification of
the class Hom or support arguments.

Validation: three clean TeX passes for the article (290 pages) and
catalogue (34 pages), no warnings or box diagnostics, with visual checks
of scalar Hom, ideal classes, duals, matrix kernels and the catalogue.
All 418 theorem/lemma/proposition/corollary/principal-summary statements,
28 example environments, 828 source labels and 1,656 auxiliary label/number
pairs are unchanged. All 4,626 anchors across 63 reports, 5,215 source-label
references and 1,814 local Markdown destinations across 226 files pass,
as does whitespace validation.

## Synchronization of the two seven-witness quartic graphs

Fast-forwarded 01e2b41 to 7ea2e32 and checked its four new modules
against the two seven-witness variants of `odg:def:cor:ctquartic`.
The generic formula selects either constant-defining quartic and adds
the squared quadratic kernel equation. A faithful ordered-ring inclusion
separates the three squares; each variant therefore defines exactly the
constant-term graph. Native integer multivariate polynomials evaluate
to the expression and have exact degree four, detected in the fresh
input variable. The implementation covers actual real omnific integers
and full ordered Hahn pullbacks containing a coefficient square root of
two. The additional Hahn theorem establishes the original quartic on
intermediate rings with precisely the integer constant intersection.
The six-witness guard variant remains pending; the ledger preserves
that distinction and makes no Gaussian single-polynomial claim.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,602 jobs; the
axiom audit checks 16,567 declarations using only propext,
Classical.choice and Quot.sound. No TeX source changed in this merge.

## Synchronization of Hahn ideal multipliers and reconstruction formulas

Merged 57d4c3e and checked its two modules against
`odg:def:lem:ainfrac`, `odg:def:thm:multiplier`,
`odg:def:eq:multiplier` and `odg:def:cor:internal`.
The support ring is exactly the ambient Hahn multipliers of the purely
infinite ideal: shifting a forbidden exponent to zero supplies a direct
counter-witness. Zero together with invertible multipliers recovers the
coefficient constants. The full coefficient pullback has a native
fraction-field embedding, and a fixed monomial places every support-ring
element in that embedded fraction field when the exponent group is
nontrivial. The fraction field is not identified with the entire Hahn field.

The literal fraction-pair formulas have their witnesses in the original
ring, are invariant under cross-multiplication equivalence, and recover
both multiplier membership and coefficient membership. Subtracting a
coefficient gives the constant-term graph. Expanding the quadratic ideal
test supplies the real and Gaussian ring-language formulas. The ledger
keeps actual surreal/surcomplex specializations pending and does not
claim a separate first-order syntax/satisfaction formalization.

Validation: LEAN_NUM_THREADS=2 lake build passes all 4,604 jobs;
the axiom audit checks 16,623 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 statement anchors across
63 reports, 5,216 source-label references and 1,816 local Markdown
destinations across 226 files pass, as does whitespace checking.
No TeX source changed in the merge, so the reviewed 290-page article
and 34-page catalogue remain current.

## Set-presentations and exact relation counts in lexicographic models

Reviewed `osq:rel:thm:presentation`, `osq:rel:lem:embedding`,
`osq:rel:thm:kappa` and `osq:rel:prop:fd`, together with the
countable-case remark `osq:rel:rem:alephzero`. The four standard
statements are unchanged; the countable remark is corrected and expanded.

The class-ring obstruction now constructs both sections of the pullback
used in Schanuel's lemma. The formula choosing a preimage of each ideal
element is only a section as a class map; applying it to the free basis
and extending finite combinations gives the needed A-linear section.
The other section uses finitely many lifts. Projecting the resulting
set-generated module onto the tail contradicts its lack of set generators.
The equational nonflatness witness is checked directly, with every proposed
relation column in the tail and every resulting coordinate in X^g Pi.

The exponent embedding is given on finite rational sums and checked by
its leading sign. The proof distinguishes the surreal exponent omega^-alpha
from the image omega^(omega^-alpha) of the ring monomial X^(e_alpha).
Regularity bounds the coordinate indices of a small family and proves
exact coinitiality, including the empty-family case. Reindexing reverse
well-ordered support verifies the ring embedding and its exact image.
The countable case extends the finite-support ring construction, without
calling the ambient finite-support collection a field.

The tail proof gives the strict-support factorization, idempotence,
directed union of principal ideals, flatness and both generator bounds.
Regularity is used explicitly for a union of fewer than kappa small
supports. The matrix decomposition transfers to the model with its actual
PID and coefficient-space hypotheses. Schanuel gives both bounds for the
kernel of every surjection from a finite free module, independently of
its generating family. These generator counts are kept separate from
the quotient-cardinality thresholds, which are asserted only for the
uncountable models.

Corrected the countable remark's phrase “every finite presentation”:
these modules are not finitely presented. The intended claim concerns
every surjection from a finite free module and its countably generated
kernel. A concrete telescope with x_n = X^(e_n) proves projective
dimension one for the tail, two for D and the lattice module, and three
for the cyclic quotient. The flat-dimension proof now exhibits a nonzero
antisymmetric tensor and performs both dimension shifts directly, so it
no longer relies on the later general coefficient-Tor formula.

Updated the root README, report guide, catalogue, notation and ledger.
The four standard results remain Pending in Lean. The later general
coefficient-Tor formula, moduli and derived classifications, and full
source reconciliation remain pending review. Standard directed-union
flatness and the equational criterion were checked against Stacks
Section 10.39, Tag 00H9; no finite computation is treated as verification
of the cardinal or class arguments.

Validation: three clean TeX passes for the article (291 pages) and
catalogue (34 pages), with no warnings or box diagnostics and visual
checks of the class pullback, embeddings, relation counts, countable
remark, flat-dimension proof and catalogue. All 418 standard/principal
statements, 828 source labels and 1,656 auxiliary label/number pairs
are unchanged; among remark environments only the intended countable
remark changes. All 4,626 anchors across 63 reports, 5,217 source-label
references and 1,816 local Markdown destinations across 226 files pass,
as does whitespace checking. No Lean source changed, so the previous
two-thread 4,604-job build and 16,623-declaration axiom audit remain
the Lean baseline for this documentation pass.

## Synchronization: actual multiplier and coefficient reconstruction

Merged origin/main through 0bd4b88 (including 2522129) after reviewing the
six incoming modules against `odg:def:lem:ainfrac`,
`odg:def:thm:multiplier`, `odg:def:eq:multiplier` and
`odg:def:cor:internal`. The transfer argument needs preimages of individual
monomials, not surjectivity onto a full Hahn field. Actual real and complex
support rings are the multipliers of their native purely infinite ideals;
zero together with invertible multipliers recovers the ordinary coefficient
fields. A nonzero augmentation-kernel element clears support-ring elements
into the native fraction field. This inclusion alone makes no claim that
the Gaussian omnific fraction image is the entire surcomplex field.

The literal fraction-pair formulas use the quadratic ideal test in the
original omnific rings. Their meanings and invariance under changing both
fraction representatives are proved, including the full coefficient-map
graph. The ledger distinguishes these semantic formulas from a separate
first-order syntax/satisfaction development and from proper-class quotient
objects. The different-radicand number-field extension remains outside
this mapping. The README and coverage entries agree with that scope.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,610 jobs; the audit
checks 16,707 declarations and permits only propext, Classical.choice and
Quot.sound. All 4,626 anchors across 63 reports, 5,217 source-label references
and 1,822 local Markdown destinations across 226 files pass. No incoming TeX
changed, so the reviewed 291-page article and 34-page catalogue remain current.

## Synchronization: actual real-structure reconstruction

Merged origin/main through e1859ca and compared the new module with
`odg:def:thm:realrecovery` and its constant-term/standard-part examples.
The interpreted coefficient predicate uses the proved omnific fraction
representation of every actual surreal. Nonzero squares reconstruct
positivity, and positive real bounds reconstruct the finite ring and
infinitesimal ideal. The standard-part graph has exactly the finite inputs
and one real output. Its examples distinguish constant extraction at
omega + 7 from standard part at 7 + omega inverse. The README and ledger
accurately record these literal semantic formulas; separate first-order
syntax, the value-group quotient and automorphism theorem are not claimed.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,611 jobs; the audit
checks 16,740 declarations using only propext, Classical.choice and Quot.sound.
All 4,626 anchors across 63 reports, 5,217 source-label references and 1,823
local Markdown destinations across 226 files pass, as does whitespace
checking. No TeX source changed; the 291-page article and 34-page catalogue
remain current.

## Coefficient-Tor maps, ranks and field detection

Reviewed `osq:rel:thm:tor`, `osq:rel:cor:twelve`,
`osq:rel:cor:selftor` and `osq:rel:prop:field`. All four statements
are unchanged. The general theorem now constructs both inclusions in
J K_M = X^h K_M, the coefficient quotient of the relation module, the
connecting tensor and a coefficient projection detecting nonzero tensors.
The dimension shift and localized exact sequence give the rank. The
proof separates A-torsion, killed by a nonzero tail monomial, from
D-torsion: the coefficient kernel is D-torsion-free. Over arbitrary D,
lattices are finite free by definition, but no freeness or finite
generation of their multiplication kernel is inferred from its rank.

Corrected the commentary that called c squared in D necessary for the
quadratic module isomorphism. It is sufficient. The more general relation
c squared = u + v c, with u and v in D, also supplies an explicit free
basis. The golden ratio is a counterexample to the claimed necessity.
The rank calculation covers every quadratic element, higher algebraic
degree and transcendental elements. The explanation of surviving tensors
now requires a nonzero coefficient relation.

The endpoint proof constructs the algebraically independent finite family,
checks the monic Eisenstein orders in both real and Gaussian cases, and
includes rank one. The field criterion defines the product span V squared
and explains the finite-dimensional inverse argument. Its example now
writes Z + Z times (1/sqrt(2)) unambiguously and proves that this lattice
is not a ring, although its rational span is a field.

Updated the root README, report guide, catalogue, notation and source
anchors. Corrected a remaining guide reference to a finite presentation
where a finite-free surjection is meant. These four results remain Pending
in Lean. The subsequent moduli, endomorphism-order and derived results,
and full reconciliation of the parallel sources, await review.

Validation: three clean TeX passes for the 293-page article and 34-page
catalogue, with no warnings or box diagnostics; visual checks of the four
proofs and catalogue. All 418 standard/principal statements, 828 labels
and 1,656 auxiliary label/number pairs are unchanged. All 4,626 anchors
across 63 reports, 5,217 source-label references and 1,823 local Markdown
destinations across 226 files pass, as does whitespace checking. No Lean
source changed, so the previous two-thread 4,611-job build and
16,740-declaration axiom audit remain the Lean baseline for this pass.

## Synchronization: the actual natural value-group quotient

Merged origin/main through 78a0502, including d0f6d88, and reviewed
NaturalValueGroup.lean against `odg:def:cor:valuegroup`. The subgroup is
proved to be exactly the image of the units of the finite-element ring.
The native quotient is externally identified with negative leading
exponents and carries a compatible linear order. Its order and equality
relations agree both with the existing valuation and with the reconstructed
finite-element formulas. The README and ledger correctly distinguish
this quotient construction from a definable monomial cross-section and
from a separate first-order syntax/satisfaction formalization.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,612 jobs; the
axiom audit checks 16,769 declarations, using only propext,
Classical.choice and Quot.sound. All 4,626 anchors across 63 reports,
5,217 source-label references and 1,824 local Markdown destinations across
226 files pass, as does whitespace checking. No incoming TeX changed,
so the reviewed 293-page article and 34-page catalogue remain current.

## Rank-two moduli, multiplier orders and tail-annihilated tests

Reviewed `osq:rel:thm:mobius`, `osq:rel:thm:order`,
`osq:rel:cor:realize` and `osq:rel:thm:augmentation`, together with
`osq:rel:ex:pell`. The four theorem/corollary statements are unchanged.
A scope paragraph restores the integer/real and Gaussian/complex pairs
before using the countable PID hypotheses; the preceding coefficient-Tor
theorem's arbitrary-D generality is not silently carried into these results.

The moduli proof writes both basis changes and the actual scalar between
different monomial scales. It verifies nonzero denominators and preservation
of the irrational parameter set. Counting the countable orbits gives
continuum many classes without assuming the continuum hypothesis; coefficient
rank two is distinguished from fraction-field rank one.

The order proof checks inverse closure of the multiplier field, its finite
degree and the vector-space dimension formula giving divisibility of the
lattice rank. Finite freeness uses the PID hypothesis. Cayley--Hamilton
proves integrality, and clearing the finitely many matrix denominators
identifies the fraction field of the order exactly. The universal quotient
uses the theorem for arbitrary unital coefficient subrings; it does not
require that this new order be a PID. Realization now explains why
endomorphisms may have tails while automorphism scalars cannot.

The Pell example verifies the generator images, inverse and infinitely
many distinct powers, and clarifies that the displayed pair is a basis of
the scaled coefficient lattice, not an omnific basis of the ideal. The
higher-degree example spells out the quadratic relation that would be
forced by a nonconstant multiplier, and lists the Gaussian units.

The augmentation proof supplies inverse tensor maps, proves annihilation
by balancing finite sums, and separates the Tor-one injection from higher
dimension shifts and flatness of the kernel. The class construction fixes
one balanced map and target at a time. The follow-up discussion now
explicitly restricts the claim about all set-sized tests to the class ring;
a half-scale monomial shows why the quotient test in a set-sized model
is not killed by the tail. Agreement with a free tensor functor on these
restricted tests does not establish flatness.

Updated the root README, guides, notation, catalogue and source anchors.
These four results remain Pending in Lean. The later derived classifications
and full source reconciliation remain pending review.

Validation: three clean TeX passes for the 294-page article and 34-page
catalogue, with no warnings or box diagnostics and visual checks of the
four proofs, example and catalogue. All 418 standard/principal statements,
828 labels and 1,656 auxiliary label/number pairs are unchanged; only the
intended Pell example changes among 28 example environments. The existing
source-17 verifier passes 347 exact finite arithmetic checks, including
16 fractional-linear basis changes and 13 Pell matrix powers; these do
not verify the cardinal or class arguments. All 4,626 anchors across
63 reports, 5,217 source-label references and 1,824 local Markdown
destinations across 226 files pass, as does whitespace checking. No Lean
source changed; the previous two-thread 4,612-job build and
16,769-declaration axiom audit remain the Lean baseline for this pass.

## Synchronization: actual omnific automorphism rigidity

Merged origin/main through c2caaca and reviewed both incoming modules
against `odg:def:thm:autreal`. Formula transport uses the inverse ring map
for the universal multiplier quantifier, retaining the source's distinction
between automorphisms and nonsurjective endomorphisms. The actual fraction
field gives the extension and its fraction formula, with uniqueness even
among field homomorphisms agreeing on the omnific ring. The reconstructed
coefficient field is preserved; real ring-homomorphism rigidity then fixes
each ordinary real. Actual square roots give order preservation, and the
existing finite-element, infinitesimal and standard-part predicates are
preserved as claimed. The README and ledger agree with these declarations;
the separate dilation example and Gaussian coefficient assertions remain
outside this mapping.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,614 jobs, and the
axiom audit checks 16,791 declarations using only propext, Classical.choice
and Quot.sound. All 4,626 anchors across 63 reports, 5,217 source-label
references and 1,826 local Markdown destinations across 226 files pass,
as does whitespace checking. No incoming TeX changed; the 294-page
article and 34-page catalogue remain current.

## Face resolutions, free telescopes and the top Ext formula

Reviewed `osq:da:prop:faces`, `osq:da:thm:telescope` and
`osq:da:thm:ext`, with all three statements unchanged. The face proof
separates the constant component, degrees outside the chosen face, and
its contractible simplex components. Finite support lets their preimages
assemble into a chain. The lower flat-dimension witness treats a singleton
face separately: the coefficient map is K to K/D with kernel D, also
when D = K. Higher faces retain K in the top Tor degree.

The telescope proof makes the principal-ideal colimit and its coefficient
scope explicit, including the singleton differential. It checks the cone
signs, injectivity of one minus shift, and the colimit cokernel. The
comparison with the flat face complex has a contractible kernel, with
both terms of the contraction identity written out. Its augmentation
sums finite stage tuples modulo the face ideal. This supplies a free
resolution without treating the individual Koszul complexes as resolutions;
the failure of regularity over a proper coefficient subring is verified.

The top-Ext proof first checks that the inverse transition descends to
the quotients. Duals of countable free direct sums are products, and
arbitrary independent functional values give the entire product of the
stage ideals as boundaries. Passing to the coordinate quotients then
gives the displayed cokernel, naturally in the target module. The
identification with the first derived inverse limit was checked against
Stacks Tags 07KV and 0CQC, now included in the existing derived-functor
bibliography entry. No Mittag--Leffler or surjectivity assumption is used.

Updated README, guides, notation, catalogue and source anchors. These
three results remain Pending in Lean. The following nonvanishing theorem,
exact projective dimensions and later derived classifications, and full
source reconciliation, remain pending review.

Validation: three clean final TeX passes for the 296-page article and
34-page catalogue, without warnings or box diagnostics, plus visual
checks of all three proofs and the catalogue. All 418 standard/principal
statements, 828 labels and 1,656 auxiliary label/number pairs are unchanged.
All 4,626 anchors across 63 reports, 5,217 source-label references and
1,826 local Markdown destinations across 226 files pass, as does whitespace
checking. No Lean source changed; the previous two-thread 4,614-job build
and 16,791-declaration axiom audit remain the Lean baseline for this pass.

## Synchronization: actual exponent automorphisms and strong sums

Merged origin/main through 233236d, including 5d891ce, and reviewed the
three incoming modules against `odg:def:ex:dilation`, `prop:hahn-lift`,
`eq:hahn-lift` and the canonical-field-lift clause of `thm:dilation`.
Ordered additive exponent automorphisms transport lower-universe-small
normal forms and induce actual field automorphisms. The coefficients and
entire support are transported, real constants are fixed, and the native
omnific subring is preserved. The restriction's fraction extension agrees
with the constructed field map. Positive exponent scalings have reciprocal
inverses; doubling moves omega and sends one plus omega to one plus omega
squared.

Strong summability is preserved and reflected for arbitrary index
universes; commutation with the actual strong sum retains the small-index
hypothesis of that sum operation. The lift transports leading exponents
and the natural valuation, including zero's infinite value, and preserves
the actual field order. The README and ledger accurately update the
canonical-lift coverage while keeping unconditional exponential non-lifting
pending construction of the global surreal exponential. No full-Hahn-field
surjectivity or exponential-preservation claim is introduced.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,617 jobs; the
axiom audit checks 16,855 declarations using only propext, Classical.choice
and Quot.sound. All 4,626 anchors across 63 reports, 5,218 source-label
references and 1,830 local Markdown destinations across 226 files pass,
as does whitespace checking. No incoming TeX changed; the 296-page article
and 34-page catalogue remain current.

## Coordinate-core nonvanishing and exact projective dimensions

Reviewed `osq:da:thm:injection`, `osq:da:cor:exactpd` and
`osq:da:thm:lattice`, retaining all three statements. The injection proof
writes the telescoping ideal containment and compares coefficients in a
single fixed polynomial. Nonzero entries of the coefficient sequence
force distinct monomials in that polynomial, hence finite support. The
converse gives explicit finite solutions. This is a D-linear injection of
the product modulo the direct sum, not a construction of infinite sums
inside the finite-support core.

The exact-dimension proof uses the nonzero constant sequence and spells
out dimension shifting for every target module. The lattice proof fixes a
basis, writes both shifts and their naturality, and treats the principal
rank-one quotient separately: multiplication by its nonzero generator
proves that the nonzero quotient cannot be flat. This includes the flat
rank-one tail of projective dimension one.

Corrected adjacent claims and the corresponding clause of
`osq:hd:q:cores`: the stronger global and weak-global lower bounds from
rank-two lattices require K different from Frac D. The new boundary
calculation proves that K[Q_{>=0}] has weak global dimension exactly one,
although its coefficient module K has projective dimension two. Finite
families lie in one polynomial subring; gcd and Bezout give principal
finitely generated ideals, the ideal criterion makes torsion-free modules
flat, and a nonzero principal quotient supplies the lower bound. The
existing Stacks flatness reference supports the criterion. The warning
about nonregular finite Koszul sequences now specifies D different from K.
The introduction, root README, report guide, catalogue and shared notation
carry the same qualifications. Later derived classifications and full
source reconciliation remain pending review; these three results remain
Pending in Lean.

Validation: three clean final TeX passes for the 297-page article and
34-page catalogue, with no warnings or box diagnostics, and visual checks
of all revised proofs and the catalogue. All 418 standard/principal
statements, 828 labels and 1,656 auxiliary label/number pairs are unchanged.
Of 66 question environments only the specified core-dimension question
changed; all 60 remarks and 28 examples are unchanged. All 4,626 anchors
across 63 reports, 5,218 source-label references and 1,830 local Markdown
destinations across 226 files pass, as does whitespace checking. No Lean
source changed; the two-thread 4,617-job build and 16,855-declaration axiom
audit remain the Lean baseline before synchronization.

## Synchronization: Gaussian fractions and the coefficient-automorphism section

Merged origin/main through f09b4df, including 59511d2 and c790d96.
Reviewed all five incoming modules against the Gaussian fraction-field
identity in `odg:def:sec:reconstruction` and following
`odg:frac:prop:gaussianfrac`, and every clause of
`odg:def:prop:coeffaut`. One positive monomial clears both coordinates of
an entire family small in the birthday universe. This supplies the actual
Gaussian omnific fraction-field instance and surjectivity of its native
fraction embedding. Ring-formula invariance then makes the unique fraction
extension of any Gaussian omnific automorphism preserve the reconstructed
ordinary complex field, with restriction a group homomorphism.

The small-Hahn realization uses the two real coordinate forms and realizes
exactly the lower-universe-small complex supports. Applying an arbitrary
complex coefficient automorphism preserves that support, so the image is
an actual surcomplex number. The field lift has the expected inverse,
fixes real Conway monomials, and preserves strong summability; strong-sum
commutation retains the small-index hypothesis. Preservation of Gaussian
integer coefficients restricts the lift to the Gaussian omnific ring.
Its fraction extension is the original field lift and its coefficient
restriction is the chosen complex automorphism. The resulting group
homomorphism is a section of restriction, completing the source
proposition. No continuity or real-axis preservation, full-Hahn-field
surjectivity, or set of all proper-class automorphisms is asserted.
The subsequent phase twist and logical nondefinability remain pending.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,622 jobs; the
axiom audit checks 16,927 declarations with only propext, Classical.choice
and Quot.sound. All 4,626 anchors across 63 reports, 5,219 source-label
references and 1,835 local Markdown destinations across 226 files pass,
as does whitespace checking. No incoming TeX changed; the locally rebuilt
297-page article and 34-page catalogue remain current.

## Flat DGA resolution and all Tor groups of two lattice quotients

Reviewed `osq:da:thm:dga` and `osq:da:thm:pair`, keeping both
statements. The resolution proof separates exactness and flatness from
its algebra structure, verifies that the degree-one product lies in the
syzygy module, and checks associativity, the unit and graded commutativity.
It writes the Leibniz identities in degrees (1,1), (1,2) and (2,1), with
opposite signs in the two mixed cases, and explains the remaining degree
pairs. The multiplicative augmentation gives the quasi-isomorphism.
Bounded flatness justifies derived tensoring; the augmentation-compatible
multiplication yields the canonical Tor product by derived base change.
Checked this against Stacks Tags 06XY and 068G and added the latter to the
existing derived-functor bibliography entry.

The pair calculation now writes degree-two cycles and their coefficient
map, proves JS = X^h S, gives lifts of every multiplication relation and
identifies the kernel. Principal-ideal-domain freeness and the localization
rank are separate steps. The dimension-two aside now requires lattice
rank at least two; principal rank-one quotients have dimension one, while
Tor vanishes above degree two in both cases. This is over the ordered core
and the class ring interpreted as a set in the larger universe, not over
the nonflat coordinate cores of dimension at least two.

For degree one, the ideal exact sequence gives (I intersect J)/IJ without
assuming the ideals flat. Each scale ordering is checked, as is the ideal
product formula. The truncation map to the constant term, open interval
and endpoint modulo MN has the displayed denominator as kernel and is
surjective. Its splitting is D-linear only. The monomial of exponent e/2
proves nonvanishing even when the constant intersection and second Tor
both vanish. Updated the root README, report guide, catalogue, shared
notation and source anchors. These two results remain Pending in Lean;
the subsequent linear-disjointness, self-Tor product, reconstruction and
shadow results, and full source reconciliation, remain pending review.

Validation: three clean final TeX passes for the 299-page article and
34-page catalogue, with no warnings or box diagnostics; inspected all
revised proof pages and the catalogue. All 418 standard/principal
statements, 828 labels, 1,656 auxiliary label/number pairs, 66 questions,
60 remarks and 28 examples are unchanged. All 4,626 anchors in 63 reports,
5,219 source-label references and 1,835 local Markdown destinations in
226 files pass, as does whitespace checking. No Lean source changed;
the two-thread 4,622-job build and 16,927-declaration axiom audit remain
the Lean baseline before synchronization. Existing finite verifiers do
not establish these general DGA and support arguments and were not used
as substitutes for the proof review.

## Linear disjointness and the integral self-Tor product

Reviewed `osq:da:lem:compositum`, `osq:da:thm:disjoint`,
`osq:da:thm:product` and `osq:da:cor:indecomposable`, preserving
all four statements. The compositum proof explains finite dimensionality,
closure under multiplication, existence of inverses, and the equality
with the fraction-field span of the product lattice. The disjointness
proof writes the exact coefficient sequence before and after localization;
torsion freeness ensures that vanishing after localization means actual
vanishing. The common-embedding convention agrees with the
[Stacks definition of linear disjointness](https://stacks.math.columbia.edu/tag/09IF).
It is not a criterion for unspecified abstract embeddings or for vanishing
of first Tor.

Expanded the boundary map's surjectivity and kernel, then computed the
self-product from actual degree-one cycles. The first-homology quotient
is identified with I/I^2 using the presentation and its image on IA^r.
The degree-two coefficient vector gives the displayed antisymmetrized
tensor precisely under the specified flip of the preceding pair-Tor
convention; using the earlier tensor order reverses the sign. Scalar
movement across tensor factors uses coefficients in D.

The alternating/symmetric proof now checks injectivity of the exterior
map in a basis, identifies the symmetric quotient kernel, and lifts every
symmetric relation. Surjectivity of the boundary map identifies the
product span exactly with the exterior image. Localization gives the
ranks. Clarified that the two halves for orders refer to ranks in an exact
sequence: the symmetric relation module is a submodule of the symmetric
quotient, not a selected submodule of symmetric tensors. A D-linear
splitting exists because the quotient is free over the PID, but no choice
is specified, and averaging by one half is not used over Z or Z[i].
Updated root README, guide, catalogue, notation and source anchors. All
four results remain Pending in Lean. Framed reconstruction, the derived
constant-term shadow and full source reconciliation remain pending review.

Validation: three clean final TeX passes for the 300-page article and
34-page catalogue, without warnings or box diagnostics, and visual
inspection of all revised proof pages and the catalogue. All 418
standard/principal statements, 828 labels, 1,656 auxiliary label/number
pairs, 66 questions, 60 remarks and 28 examples are unchanged. The source-21
finite verifier exactly reproduces the delivered JSON: 1,008 finite
Koszul/transition identities, 600 finite telescope/support checks and the
four arithmetic examples, including the product/indecomposable ranks.
These finite checks do not establish the general module, localization
or infinite-support arguments. All 4,626 anchors in 63 reports, 5,219
source-label references and 1,835 local Markdown destinations in 226
files pass, as does whitespace checking. No Lean source changed; the
two-thread 4,622-job build and 16,927-declaration axiom audit remain the
Lean baseline before synchronization.

## Synchronization: actual character and phase twists

Merged origin/main through e6f13a0, including 4f52bfb, and reviewed all
three incoming modules against `odg:def:lem:twist`, its preceding character
construction, and the witnesses used by `odg:def:thm:norealaxis`.
The generic Hahn construction multiplies coefficients by an additive
character with nonzero values, preserves full support, and checks the
finite convolution antidiagonals; the inverse character supplies the
inverse. Small-support realization then gives an actual surcomplex field
automorphism. It fixes ordinary complex constants and the zero coefficient,
hence restricts to a Gaussian omnific automorphism fixing Gaussian integers.

The phase character uses the additive zero-coefficient map on actual
surreal exponents and only the ordinary complex exponential. Its value
at one is i. The values on omega, inverse omega and one explicitly show
that the additive coefficient map is not multiplicative. The twist sends
omega to i times omega, outside the entire actual real axis, and fails
to commute with conjugation there. Its Gaussian restriction moves the
omnific omega outside the embedded real omnific ring. The README and ledger
correctly distinguish these algebraic obstruction witnesses from the
still-pending first-order nondefinability theorem. No global surreal
exponential or unrestricted full-Hahn surjectivity is assumed.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,625 jobs; the
axiom audit checks 16,987 declarations with only propext, Classical.choice
and Quot.sound. All 4,626 source anchors in 63 reports, 5,219 source-label
references and 1,839 local Markdown destinations in 226 files pass, as
does whitespace checking. No incoming TeX changed; the newly verified
300-page article and 34-page catalogue remain current.

## Framed reconstruction and the derived constant-term shadow

Reviewed `osq:da:thm:reconstruction` and `osq:da:thm:shadow`, retaining
both statements. Reconstruction now writes the multiplication map and its
unit section, proves uniqueness of the recovered product, and checks both
directions of the isomorphism criterion, including equality of kernels
using the inverse. It distinguishes the embedded relation module and its
distinguished unit from the abstract second-Tor isomorphism type.

Expanded the integral basis argument: integrality and integral closedness
give o intersect Frac D = D; this makes o/D1 torsion free, hence free over
the PID, so the unit extends to a D-basis. Distinct unit pivots and reduction
to the first tensor row prove an integral basis of the multiplication
kernel. The quadratic, golden-ratio and cubic examples now have separated
relation and trace calculations. The cubic alternating-plus-square basis
is proved to span integrally, and Gaussian conjugation is explicitly
semilinear over Z[i]. Exact checks recompute all four delivered arithmetic
records and verify change-of-basis determinants -1 for their combined
bases, as well as discriminants 8, 12, -108 and 5. These determinant checks
address integral spanning, beyond rational rank alone.

The shadow proof spells out tensor associativity and idempotence of the
tail, including a balanced-tensor argument valid for torsion coefficient
modules. It identifies the actual two-term complex, the degree-one shift
convention and, for E = D, the square-zero multiplication. No algebra
structure is assigned to arbitrary coefficient modules. A lattice
isomorphism induces a shadow isomorphism without preserving order products.

Made the universe qualification explicit in the closing discussion.
The literal class statement about all set-sized modules translates to
lower-universe-small modules; it cannot include every module formed in
the larger universe. The regular module is a counterexample there, since
Pi A = Pi is nonzero. The ordered core has its separate small-target
counterexample from the coefficient-sum augmentation. The shadow theorem
retains its specified constant-term action hypothesis. Updated the root
README, guide, catalogue, notation and source anchors. Both results remain
Pending in Lean; the subsequent polyhedral-core results and full source
reconciliation remain pending review.

Validation: three clean final TeX passes for the 302-page article and
34-page catalogue, with no warnings or box diagnostics; inspected the
revised proofs, examples, universe qualification and catalogue. All 418
standard/principal statements, 828 labels, 1,656 auxiliary label/number
pairs, 66 questions, 60 remarks and 28 numbered examples are unchanged.
All 4,626 source anchors in 63 reports, 5,219 source-label references and
1,839 local Markdown destinations in 226 files pass, as does whitespace
checking. No Lean source changed; the two-thread 4,625-job build and
16,987-declaration axiom audit remain the baseline before synchronization.
Finite example calculations do not establish the general reconstruction,
derived-category or universe-relative assertions.

## Synchronization: full first-order real-axis nondefinability

Merged origin/main through b8f4328, including 4fabd72, and reviewed the
two new modules and the phase-twist docstring update against every clause
of `odg:def:thm:norealaxis`. The generic invariance theorem uses Mathlib's
native parameter-set definability and formula semantics for arbitrary
formulas. It transports both definable tuple sets and function graphs
under automorphisms fixing the entire parameter set.

The actual surcomplex structure is explicitly the ring language with a
unary predicate for the Gaussian omnific image. The phase twist preserves
and reflects this predicate, fixes every ordinary complex parameter, and
is packaged as an automorphism of that language. The existing omega
witness disproves definability of the real axis; failure to commute with
conjugation disproves definability of its graph. Equivalent statements
in the expanded language name every ordinary complex constant. The pure
Gaussian omnific ring has its own language automorphism and the ordinary
Gaussian integer parameter set; the moved omnific omega proves the real
omnific subring is not definable there. The README and ledger now correctly
mark the full theorem proved, including quantified formulas, rather than
only its algebraic witnesses. The scope remains the actual universe-indexed
carriers; no proper-class first-order structure is introduced.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,628 jobs; the
axiom audit checks 17,035 declarations using only propext, Classical.choice
and Quot.sound. All 4,626 anchors in 63 reports, 5,219 source-label
references and 1,841 local Markdown destinations in 226 files pass,
as does whitespace checking. No incoming TeX changed; the reviewed
302-page article and 34-page catalogue remain current.

## Resynchronization: native arithmetic guards and quantifier translation

The first push was rejected because main advanced. Fetched and merged
77e2ff4, then reviewed its three modules against `odg:def:cor:arithmetic`
and the referenced integer and natural guards. Explicit native ring terms
and formulas encode the three Xi equations with five witnesses and the
additional four-square condition. Their semantics identify exactly the
ordinary integer and natural images, without nonlogical parameters.

The generic transformation recursively guards every universal quantifier
and relabels its variable without capture. Formula induction proves truth
preservation along a first-order embedding whose image has that guard;
the embedding need not be elementary. Applied to the actual integer
inclusion, this gives one syntactic translation valid at every carrier
universe and for every standard free and bound assignment, including
integer ring sentences. The README and ledger retain the precise partial
scope: the dedicated natural-arithmetic translation, encoded computability,
many-one reduction, undecidability and non-axiomatizability remain Pending.

Validation: the repeated `LEAN_NUM_THREADS=2 lake build` passes all
4,631 jobs, and the axiom audit checks 17,116 declarations using only
propext, Classical.choice and Quot.sound. The final audits pass for all
4,626 anchors in 63 reports, 5,219 source-label references and 1,844 local
Markdown destinations in 226 files, plus whitespace. No additional TeX
changed, so the 302-page article and 34-page catalogue remain current.

## Polyhedral cores: embeddings and flat face ideals

Reviewed the first five results of Section 13.11 in the omnific-quotient
report: `osq:pc:prop:embedding`, `osq:pc:prop:fractions`,
`osq:pc:lem:subtract`, `osq:pc:thm:exhaustion` and
`osq:pc:thm:products`. Their statements are unchanged. The embedding proof
constructs a strictly positive rational functional from the facets and
checks the dual-basis lexicographic map, including dimension one and the
Gaussian coefficient case. Corrected the surrounding prose to restrict
the asserted embedding into Oz to (D, K) = (Z, R), as the proposition
requires; arbitrary coefficient fields, including positive characteristic,
cannot all embed there. The fraction-field proof identifies the fields
inside the given group-algebra fraction field and supplies the rational
interior shift that recovers every group monomial and every coefficient.

Face subtraction now has an explicit positive bound from the finite facet
ratios, with the same least face and a nonzero difference. The ideal
definition explains closure under multiplication and separates the zero-face
convention from the tail-only formula. Principal exhaustion uses one shift
for the whole finite support, preserving nonzero residual exponents so
arbitrary K-coefficients remain allowed. Expanded the obstruction to finite
generation, both exactness checks in the free telescope, and the dual-basis
argument ruling out projectivity. Products retain their arbitrary coefficient
in a nonconstant factor; flatness supplies the tensor injection, and testing
an interior monomial proves the reverse face-inclusion implication.

Updated the root README, report guide, catalogue, notation and source
anchors. These are manuscript proofs over any unital subring D of a field K;
no field, Noetherian or PID hypothesis on D is added. Their Lean proofs
remain Pending. The subsequent radical classification, face resolutions,
dimension formulas and full source reconciliation remain pending review.

Validation: three clean final TeX passes for the 303-page article and
34-page catalogue, with no warnings or box diagnostics; inspected all
revised proof pages and the catalogue entry. All 418 standard/principal
statements, 828 labels, 1,656 auxiliary label/number pairs, 66 questions,
60 remarks and 28 numbered examples are unchanged. All 4,626 source
anchors in 63 reports, 5,219 source-label references and 1,844 local
Markdown destinations in 226 files pass, as does whitespace checking.
No Lean source changed; the two-thread 4,631-job build and
17,116-declaration axiom audit remain the baseline before synchronization.

## Synchronization: natural arithmetic in omnific and intermediate rings

Merged origin/main through 13c9f6f, including 5c21c5f, and reviewed all
five new modules against `odg:def:cor:arithmetic`. The source language
has exactly zero, one, addition and multiplication, so the natural-number
inclusion is a first-order embedding. A change-of-language version of
relativization permits the guard to use the richer ring language. Formula
induction proves the translation preserves truth at every standard natural
assignment, including arbitrary quantifier alternations and sentences.

The same parameter-free translation applies to the actual omnific carrier
at every universe and to every integer-constant intermediate Hahn ring
over an ordered coefficient field. For the latter, mapping four-square
witnesses to the coefficient field proves positivity without requiring
constant extraction to land back in the intermediate ring. Both integer
and natural domains are natively definable there. The README and ledger
accurately retain the distinction between this syntactic/semantic result
and computability on encoded syntax: the many-one reduction, undecidability
and non-recursive axiomatizability remain Pending.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,636 jobs, and
its axiom audit checks 17,202 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 source anchors in 63 reports,
5,219 source-label references and 1,849 local Markdown destinations in
226 files pass, as does whitespace checking. No incoming TeX changed;
the 303-page article and 34-page catalogue remain current.

## Polyhedral cores: radical ideals and reduced flat resolutions

Reviewed the next six results of Section 13.11 in the omnific-quotient
report: `osq:pc:thm:radical`, `osq:pc:prop:faceprime`,
`osq:pc:thm:cech`, `osq:pc:lem:diagonal`,
`osq:pc:lem:cancellation` and `osq:pc:lem:crosscut`. Their statements
are unchanged. The classification proof now spells out the facet bound
propagating membership, the role of coefficient-fullness, and the prime
face-deletion maps that prove radicality for every finite sum. Complements
are taken in the full face poset, including zero; admitting all nonzero
faces gives the tail prime with quotient D. The face-prime proof supplies
both support implications and the minimal-ray characterization.

The simplex resolution has its augmentation, differential signs and
degreewise contraction written out, including the empty subset, the
constant degree over D and degrees outside the cone. Finite supports
justify the passage to ungraded exactness. The diagonal-block proof
identifies the relative augmented chain complex and explains both shifts
in reduced H_(p-2), including the one-generator H_(-1) contribution.

The cancellation proof gives the invertible block coordinate changes,
Schur complement, neighboring differentials and contraction of the
isolated pair. Scalars in K act A-linearly on the nonzero face ideals
even when absent from D; maps into A land in its coefficient-full tail,
so no K-vector-space structure on A is assumed. Label containment makes
the corrections legal and prevents a cancellation from changing other
diagonal homologies. The crosscut proof verifies both order maps, their
composites and the prism homotopy, treats empty complexes, and derives
the local dimension bound from strict chains of geometric faces.

Updated README, guide, notation, catalogue and source anchors. Reran the
delivered source-26 verifier from an unchanged scratch copy: all 52,080
exact assertions and all 70 recorded examples match (excluding elapsed
time), including 188 face quotients, 1,329 additional antichains,
56 contractible-pair cancellations and 2,457 rational cap checks.
These finite rational calculations support the implementation and signs;
they do not establish the general ring theorems or review the later
face-isolation and sharp-dimension proofs. Those proofs and full source
reconciliation remain pending review; the six results remain Pending
in Lean.

Validation: three clean final TeX passes for the 305-page article and
34-page catalogue, with no warnings or box diagnostics; inspected the
revised proof pages and catalogue entry. All 418 standard/principal
statements, 828 labels, 1,656 auxiliary label/number pairs, 66 questions,
60 remarks and 28 numbered examples are unchanged. All 4,626 source
anchors in 63 reports, 5,219 source-label references and 1,849 local
Markdown destinations in 226 files pass, as does whitespace checking.
No Lean source changed; the two-thread 4,636-job build and
17,202-declaration axiom audit remain the baseline before synchronization.

## Synchronization: positive-existential collapse for coefficient pullbacks

Merged origin/main through e575ccd, including 24222b9, and reviewed the
three new modules against `odg:def:thm:collapse` and its parameter example.
The logical layer uses native formulas in the existing equality-based
positive-existential fragment, which is the full positive-existential
fragment for the pure ring language. Fixed-parameter endomorphisms preserve
the defined tuple sets; composing a split retraction with its section
therefore obstructs a definition containing a kernel point but excluding
zero. The atomic equality with a named point proves why the parameter
restriction matters.

For full Hahn coefficient pullbacks, every ordinary coefficient parameter
is fixed. A negative-exponent monomial supplies the nonzero purely infinite
witness when the ordered group is nontrivial, and its leading coefficient
makes it positive over an ordered coefficient field. This proves all
displayed nonzero, nonconstant, punctured-ideal and positive-cone clauses.
The actual real and Gaussian omnific constant retractions instantiate the
general obstruction; existing real nonzero and positivity results combine
with the new nonconstant and punctured-ideal instances, and all three
Gaussian instances are explicit. The README and ledger correctly mark
the full source theorem Proved while keeping the later quantifier-free
and omitted-type results Pending. The result concerns the specified
positive-existential fragment, not arbitrary first-order nondefinability.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,639 jobs, and
its axiom audit checks 17,258 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 source anchors in 63 reports,
5,219 source-label references and 1,852 local Markdown destinations in
226 files pass, as does whitespace checking. No incoming TeX changed;
the 305-page article and 34-page catalogue remain current.

## Polyhedral cores: detecting exact dimensions and homological epimorphisms

Reviewed `osq:pc:thm:isolation`, `osq:pc:thm:exactfd`,
`osq:pc:cor:pdbounds` and `osq:pc:thm:homological` in Section 13.11
of the omnific-quotient report. Their statements are unchanged. The cap
module proof now identifies the graded principal-ideal tensors, all
degree shifts and transition multiplications, the support obstruction
for faces outside G, the cap equality for proper subfaces, and the
cofinal system of copies of K with identity maps when the labels agree.

The exact-dimension proof verifies that the maximum is defined, computes
the zero-differential detecting component, and explains why its nonzero
homology is part of ordinary ungraded Tor. It obstructs every shorter
flat resolution, with no grading or finite-generation restriction on
competitors. Truncation and Tor dimension shifting give the ideal formula,
including the flat length-one case. Explicit syzygies and the Ext
inequality prove the projective upper bound; the dual-basis finite-generation
criterion gives the lower bound of two. The one-face quotient therefore
has flat dimension one and projective dimension two.

The homological-epimorphism proof gives the degree-zero tensor isomorphism
and its inverse, kills each positive face summand by the balanced-tensor
quotient, and checks nonflatness using multiplication by a killed nonzero
monomial. Corrected the surrounding claim about cap modules: only the
detecting labels are necessarily outside the quotient-module class. A cap
on G is a module over A/r_F exactly when G contains none of the defining
antichain faces. For the first coordinate-ray ideal in the two-dimensional
orthant, second-ray caps are quotient modules; first-ray caps detect Tor_1.
The new explanation proves both directions of this criterion.

Replaced “usually not finitely generated” by the exact criterion: a cap
module is finitely generated over A exactly when K is finitely generated
as a D-module. The constant-term quotient proves necessity; constant
generators and the action on 1 generate every surviving term for sufficiency.
In particular D = K gives a cyclic module. Updated README, guide, notation,
catalogue and source anchors. These are manuscript proofs; the four source
results remain Pending in Lean. The topology and multiplicities of face
quotients, later classifications and full reconciliation remain pending
review. The preceding pass's unchanged source-26 finite-check baseline
does not establish these arbitrary-module or homological-dimension claims.

Validation: three clean final TeX passes for the 307-page article and
34-page catalogue, with no warnings or box diagnostics; inspected the
revised proofs, cap qualifications and catalogue entry. All 418
standard/principal statements, 828 labels, 1,656 auxiliary label/number
pairs, 66 questions, 60 remarks and 28 numbered examples are unchanged.
All 4,626 source anchors in 63 reports, 5,219 source-label references
and 1,852 local Markdown destinations in 226 files pass, as does whitespace
checking. No Lean source changed; the two-thread 4,639-job build and
17,258-declaration axiom audit remain the baseline before synchronization.

## Synchronization: quantifier-free lower bounds and failure of elimination

Merged origin/main through f2d0fda, including ec8aa5b, and reviewed all
five new modules against `odg:def:prop:notqf`. Native ring terms are
interpreted as univariate polynomials, with evaluation commuting with
realization. Polynomial root finiteness and induction on native IsQF,
including Boolean implication, show that any unary quantifier-free
definition with arbitrary ring parameters is finite or cofinite.

A split retraction with a nonzero kernel point in characteristic zero
supplies infinite and coinfinite kernel and coefficient-image sets.
Positive natural multiples of that point suffice; infinitely many
different exponents are not needed. The generic obstruction specializes
to every full Hahn pullback with a nontrivial exponent group and to both
actual omnific carriers, using their existing monomial witnesses.

The complete-theory consequence has an explicit native witness: no
quantifier-free unary formula is semantically equivalent to the already
constructed Xi formula modulo the complete theory. The integer and
Gaussian cases use the proved constant-definition equivalences. Thus
the README and ledger's full-Proved status includes the quantifier-
elimination obstruction, not merely the infinite/coinfinite prerequisites.
No optimal degree or witness-count bound is inferred, and the following
omitted-type theorem remains Pending.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,664 jobs, and
its axiom audit checks 17,316 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 source anchors in 63 reports,
5,219 source-label references and 1,857 local Markdown destinations in
226 files pass, as does whitespace checking. No incoming TeX changed;
the 307-page article and 34-page catalogue remain current.

## Polyhedral face topology and the cellular resolution

Reviewed and expanded `osq:pc:lem:complement`, `osq:pc:lem:outside`,
`osq:pc:thm:facebetti` and `osq:pc:prop:cellular`. The boundary-complement
proof now supplies the continuous radial map from normalized facet
inequalities, proves that its contraction avoids the deleted face and
zero vector, and gives the barycentric weights for a strong deformation
retraction onto the required order complex. The outside-vertex proof
checks the domains, nonemptiness and inequalities for both order maps.
The point section is treated separately as the augmented empty-face
complex, with reduced homology K in degree minus one.

The multiplicity proof first separates faces with no active rays and
faces whose active rays join strictly below them. Neither is a join
label, so neither acquires an unintended degree-minus-one class.
For actual labels, a positive section identifies the proper-join complex
with the outside-vertex complex. Disjoint faces contribute their boundary
sphere class; nonempty proper intersections give contractible complexes.
The proof then applies cancellation and exact flat dimension, including
D at the zero face and the free identity quotient at the whole cone.

The cellular proof specifies orientations, incidence maps and both
augmentations. Every nonzero exponent gives the augmented cellular
complex of a nonempty convex section, with cellular degree p-1 in
homological degree p. Finite supports give ungraded exactness. Tensoring
with the top-face cap leaves K in degree d, a nonzero part of ordinary
Tor, and independently proves the lower bound fd D >= d.

Corrected four ancillary projective-dimension passages and the source
comparisons: pd A_C(F) = d - dim F + 1 requires F to be proper in a
simplicial cone. At F = C the quotient is A_C itself and pd = fd = 0.
The nonempty-coordinate-set hypothesis in source 21 does not prove an
endpoint for arbitrary radical geometric quotients. Shared notation now
separates the quotient A_C/I_F by a single flat face ideal from the
quotient A_C(F) retaining a face.

Also corrected the later boundary-quotient commentary: A_C/I_C is
reduced, but in dimension one it is the domain D and is a face-prime
quotient. In dimension at least two, choose a facet, a ray outside it
and a point in its relative interior. The two boundary monomials survive
while their sum exponent is interior, giving explicit zero divisors.
This local correction does not claim review of the later classifications
or all the examples.

Updated root README, report guide, shared notation and catalogue, and
refreshed the ledger's source anchors. These are manuscript proofs:
the four source results remain Pending in Lean. The flat-ideal
classification, simpliciality criterion and full source reconciliation
remain pending review. No finite computation is offered as a proof of
these general topological or arbitrary-module assertions.

Validation: three clean final TeX passes for the 308-page article and
34-page catalogue, without warnings or box diagnostics; inspected the
revised proof pages, boundary exceptions and catalogue entry. All 418
standard/principal statements, 828 labels, 1,656 auxiliary label/number
pairs, 66 questions, 60 remarks and 28 numbered examples are unchanged.
All 4,626 source anchors in 63 reports, 5,219 source-label references
and 1,857 local Markdown destinations in 226 files pass, as does whitespace
checking. No Lean source changed locally; the 4,664-job two-thread build
and 17,316-declaration audit remain the baseline before synchronization.

## Synchronization: the explicit finitely satisfiable omitted type

Merged origin/main through da91587, including 10494f3, and reviewed all
six new modules against `odg:def:thm:saturation`. The native unary type
contains the explicit Xi guard and all nonzero integer-polynomial
inequalities. Signed numerals, powers and finite-sum terms have proved
realization semantics. A finite family of integer polynomials has a
common nonroot among zero through the sum of its degrees; its image
works in any characteristic-zero commutative ring. The native finite-
subset theorem handles finite collections of formulas, not merely an
externally supplied list of polynomials.

Algebraicity excludes realization of the full type. Quadratic integers
have an explicit degree-two integer annihilator. The number-field result
clears denominators via Mathlib's fraction-field algebraicity theorem
and handles any injectively embedded coefficient ring; its conclusion
is conditional on a native formula defining the coefficient image.
Integer and Gaussian intermediate Hahn rings use their established Xi
definitions without a constant-retraction or nontrivial-exponent-group
hypothesis. Independent theorems apply to both actual universe-indexed
omnific carriers.

The ledger correctly records Prerequisites proved for the full source
theorem: effective coding, computability of membership in the type,
recursive saturation and the tailored number-field guard remain pending.
The noncomputable polynomial representation is not used to claim an
effective syntactic construction. The root README maintains that scope.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,670 jobs;
the axiom audit checks 17,404 declarations using only propext,
Classical.choice and Quot.sound. All 4,626 source anchors in 63 reports,
5,219 source-label references and 1,863 local Markdown destinations in
226 files pass, as does whitespace checking. No incoming TeX changed;
the 308-page article and 34-page catalogue remain current.

## Synchronization retry: canonical polynomial syntax and type recognition

The first push was rejected because origin/main advanced. Merged 9215b7c
and reviewed its four modules against the computable-syntax paragraph of
`odg:def:thm:saturation`. Nonempty signed coefficient lists with nonzero
last entry correspond bijectively to nonzero integer polynomials, and
the generated terms equal the previous native polynomial syntax.

Structural formula equality covers bound variables. The parser extracts
a candidate coefficient list, checks canonicity and regenerates the
entire input formula; its correctness theorem concerns exact syntactic
membership in the omitted type, not arbitrary logical equivalence.
The recognizer and its exported decision procedure are computational.
Coefficient lookup and canonical-list validity are separately proved
primitive recursive in Mathlib's integer/list encodings.

The ledger and README correctly keep the native-formula encoding and
computability of the entire recognizer, the recursive-saturation
consequence and the tailored number-field guard pending. Updated the
earlier collapse row's stale blanket Pending reference to point to these
specific mappings. No claim about encoded formula computability follows
solely from the existence of the executable Lean decision procedure.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,677 jobs and
its axiom audit passes for 17,524 declarations with only propext,
Classical.choice and Quot.sound. All 4,626 source anchors, 5,219
source-label references and 1,867 local Markdown destinations in 226
files pass, along with whitespace checks. No incoming TeX changed;
the 308-page article and 34-page catalogue remain current.

## Flat radical ideals, marked reconstruction and simpliciality

Reviewed and expanded `osq:pc:thm:flatclass`, `osq:pc:cor:reconstruct`,
`osq:pc:thm:simplicial`, `osq:pc:cor:simplicialface` and
`osq:pc:thm:cubes`, with the adjacent square/cube/octahedron examples.
The flatness proof now displays Tor dimension shifting for every module.
For an antichain with at least two members, a minimal pairwise join G
forces every pair of generators below G to join to G. No such generator
can equal G. The proper-join complex is therefore t isolated vertices,
whose augmented sum map K^t -> K has kernel dimension t-1. Nonzero
beta_(2,G) gives flat dimension at least two over every allowed field.

The reconstruction proof gives the bijection between nonzero faces and
flat radical geometric ideals, separately adjoins the unit ideal for
the zero face, and checks order reversal and tensor multiplication,
including the unit cases. The reconstructed data are marked ideals and
inclusions, not merely abstract module isomorphism classes or an
unmarked ring.

The simpliciality proof treats both directions and all equivalences.
Facets of a simplicial cone omit one basis ray. Conversely, pointedness
makes the common zero locus of the facet functionals trivial; a facet
omitting a given ray has a functional isolating its coefficient in any
linear relation among rays. All ray generators are independent and,
by full dimensionality, form a basis. The dimension-one case is explicit.
A square cone times a ray is a four-dimensional, five-ray counterexample
to testing only one facet: its square-cone facet omits exactly one ray
and has a flat face-prime ideal, though the cone is not simplicial.

The simplicial face formula now identifies the unique complementary
face in basis coordinates, including the zero and whole-cone faces.
The cube proof verifies the positive section, dimensions and opposite
facets, including n=1, then proves both bounds for flat dimension n.
The omnific specializations are isomorphisms onto the finite-support
core images; no module dimension is transferred to the whole ambient
omnific ring.

Replaced the dense example list by a table of eight flat summand-count
patterns and explained their face counts. In a cube, a face avoids a
fixed facet exactly when it lies in the opposite facet. The counts are
for flat resolutions, not minimal free ranks. Clarified that the d-1
bound concerns quotients retaining a nonzero proper face. Updated the
root README, report guide, notation and catalogue, and refreshed source
anchors. These five manuscript results still have no Lean proofs here;
squarefree transfer, coefficient dependence, arithmetic modules, nonflat
embeddings and full source reconciliation remain pending review.

Validation: three clean final TeX passes for the 309-page report and
34-page catalogue, with no warnings or box diagnostics. Inspected the
five revised proofs, the comparison table and its explanation, and the
catalogue entry. All 418 standard/principal statements, 828 labels,
1,656 auxiliary label/number pairs, 66 questions, 60 remarks and 28
numbered examples are unchanged. The delivered source-26 verifier was
rerun unchanged in scratch: all 52,080 assertions and 70 examples match
its recorded output, excluding elapsed time. It checks 188 face quotients,
1,329 additional antichains, 56 cancellations and 2,457 rational cap
calculations; these finite rational checks are not proofs of the general
ring or characteristic-independent assertions. All 4,626 source anchors
in 63 reports, 5,219 source-label references and 1,867 local Markdown
destinations in 226 files pass, along with whitespace checks. No Lean
source changed locally; the two-thread 4,677-job build and 17,524-
declaration axiom audit remain the baseline before synchronization.

## Squarefree transfer, coefficient dependence and arbitrary arithmetic modules

Reviewed and expanded `osq:pc:cor:squarefree`,
`osq:pc:cor:coefficients`, `osq:pc:prop:scalar` and
`osq:pc:thm:arithmetic`. The squarefree proof checks that the minimal
supports form a nonempty antichain of nonempty sets. Taking a least common
multiple corresponds exactly to taking their union, identifying its
monomial label with a coordinate face. The minimal lcm label 1 is the
zero face; an atom gives augmented homology in degree minus one and a
Betti contribution in degree one. The crosscut comparison identifies the
open intervals with the proper-join homology. The external citation now
specifies Theorem 2.1 of Gasharov--Peeva--Welker; its p-2 shift was checked
against the publisher-indexed theorem statement. Taylor-resolution labels
exclude all other multidegrees. Scalar cancellation and tensoring a minimal
free resolution with the residue field explain why the last Betti degree
is ordinary projective dimension on the polynomial side. The previously
proved cap theorem makes that degree ordinary flat dimension on the core
side. Projective dimension itself is not transferred.

The coefficient proof uses minors of the augmented integer boundary
matrices to show equality of rank over a field and its prime subfield.
The homology-dimension formula includes the empty-face augmentation.
The constant subring D does not occur in those matrices. The real and
Gaussian cases agree because both coefficient fields have characteristic
zero; no equality across all characteristics is asserted.

For scalar quotients the kernel of the constant map modulo a is explicit.
The domain property supplies the two-term free resolution. If a is a
nonunit of D, the quotient is nonzero and tensoring the injection given
by multiplication by a produces a noninjective zero map. This proves
both dimensions equal one and separates the unit/zero-quotient case.

The arithmetic proof handles arbitrary, possibly infinitely generated
modules. Finite torsion submodules decompose over the PID; filtered
colimits preserve the required Tor vanishing. A killed nonzero element
proves nonflatness in the torsion case. The quotient by torsion is proved
torsion free, hence flat over D. Tensoring the cellular resolution with
it preserves exactness; the degree-zero term is flat by base change and
each positive term is a possibly infinite direct sum of flat face ideals.
The cap isolates K tensor_D V in the top degree. Localization at Frac D
followed by field extension to K proves its nonvanishing.

To pass back to a mixed module, multiplication by a nonzero scalar is an
isomorphism on the cap module, so all Tor groups against the torsion part
vanish, including degree zero. That degree-zero clause makes the long
exact sequence work in cone dimension one. No splitting of the torsion
sequence is assumed. The upper bound is checked against every target
module, and the nonzero homogeneous detector belongs to ordinary Tor.

Updated root README, guide, shared notation and catalogue. Replaced an
outdated blanket pending-review sentence in the ledger with links to the
current guide and reconciliation, and refreshed the source anchors.
The four manuscript statements are unchanged and remain Pending in Lean.
The lattice-module remark, nonflat embeddings and full source
reconciliation remain pending review.

Validation: three clean final TeX passes for the 311-page article and
34-page catalogue, with no warnings or box diagnostics; inspected all
four revised proofs and the catalogue entry. All 418 standard/principal
statements, 828 labels, 1,656 auxiliary label/number pairs, 66 questions,
60 remarks and 28 numbered examples are unchanged. All 4,626 source
anchors in 63 reports, 5,219 source-label references and 1,869 local
Markdown destinations in 226 files pass, along with whitespace checks.
The preceding pass's finite rational verifier remains unchanged and is
not evidence for the new arbitrary-module or all-characteristic proofs.
No Lean source changed locally; the two-thread 4,677-job build and
17,524-declaration axiom audit remain the baseline before synchronization.

## Synchronization: primitive-recursive native ring-term codes

Merged origin/main through 9e70115, including d52c892, and reviewed its
three modules against the effective-syntax step of `odg:def:thm:saturation`.
Prefix tokens distinguish natural-number variables and all five ring
function symbols. Stack parsing rejects missing arguments and leftover
terms. Both round trips hold, including exact reconstruction of the
whole input after successful decoding; malformed suffixes are not ignored.

The numerical stack-height scan is proved primitive recursive and
characterizes precisely the encoder's range. The equivalence with valid
prefix streams supplies an explicit local Primcodable instance using
Mathlib's existing token/list encodings. Under that instance, the native
term code is definitionally the token-list code, and both encoding and
decoding are proved primitive recursive. Variable, negation, addition
and multiplication constructors have corresponding proofs. Natural and
signed numerals, powers and finite coefficient-list polynomial terms are
primitive recursive with these exact native constructors, rather than
only semantically equivalent expressions.

The new mapping accurately remains Prerequisites proved for the full
omitted-type computability clause. Bounded-formula coding and variable
scopes, the complete membership recognizer and the recursive-saturation
consequence remain pending. The local encoding does not replace other
Mathlib encodings globally. No incoming manuscript changed.

Validation: `LEAN_NUM_THREADS=2 lake build` passes all 4,680 jobs and
the axiom audit passes for 17,621 declarations, using only propext,
Classical.choice and Quot.sound. All 4,626 source anchors in 63 reports,
5,219 source-label references and 1,872 local Markdown destinations in
226 files pass, together with whitespace checks. The 311-page article
and 34-page catalogue remain current.

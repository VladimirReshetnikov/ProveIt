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

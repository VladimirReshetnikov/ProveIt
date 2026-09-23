# Diophantine source reconciliation and proof review

This record covers the elementary source comparison in Sections 1–4 of the
maintained [article](article.tex), followed by proof reviews of the original Sections 5–12.
After the three expansions, the reviewed original Sections 11–12 are Sections
14 and 19; the fractions section is Section 15, and the curve and differential
rigidity part is Sections 16–18.
Subsequent passes review the newly added Sections 11–13 from sources 06–07.
Further passes review all of Section 15 from sources 08–09 and the
Gaussian-fiber and étale-norm additions in Section 6 from sources 07 and 13.
A further pass reviews source 07's quartic in Section 10 and the
elementary ring and Euler subsections 16.2–16.3. The subsequent pass
reviews the squarefree certificate and Weierstrass applications in
Section 16.4. The next pass covers Section 16.5 through inheritance,
completing the maintained Section 16 proof chain. Sections 17–18,
their pointers in Sections 6, 7 and 14, and Sections 20–21 remain
outside the completed proof review.
It does **not** certify integration of every result in the thirteen manuscripts
or review of all later proofs and imported classical results. Section numbers
below are those current when each pass was made; the last section gives the
present numbering. The geometric curve proofs and all of Sections 17–18
remain outside these passes; the review of Section 16 now includes
the two-ring principle, symmetric differentials and inheritance.

## Recoverable sources

The original ZIP files are tracked at commit `f0b7f43` under `docs/new/`.
Commit `be06fc8` placed their supplementary files here and installed source 01
as the article, without merging the other two texts.

| Source | Archive | TeX member |
|---|---|---|
| 01 | `omnific_integers.zip` | `omnific_integers/omnific_integers.tex` |
| 02 | `omnific_integers_diophantine.zip` | `omnific_integers_diophantine/article.tex` |
| 05 | `omnific_integers_article.zip` | `omnific_integers/article.tex` |

The source-01 extraction was byte-identical to the installed base before
the elementary review in `7784f7f`. That review retained all 41 base standard
statements and added four. Concurrent commit `bbdd536` assembled sources
01, 02 and 05 more broadly into a 67-statement article. The merge `1186c11`
uses that expanded text and preserves the reviewed support, quotient and
nilpotent-image clarifications. The notation is now `Oz = ℤ ⊕ Π`, agreeing
with the foundations report; `J` below denotes the same ideal in the earlier
review and source 01. The 67 standard statements do not count the separately
styled cited theorem, remarks, examples and questions.

All 81 labels from the elementary review still resolve. Nine are aliases
for renamed or combined locations: `odg:cor:Jglobal` points to
`odg:cor:Pglobal`; `odg:cor:commonmultiples` to `odg:cor:projectiveclear`;
`odg:prop:nogcd` to the retained degree proof `odg:rem:nogcd01`;
`odg:cor:powers` to `odg:rem:powers`; `odg:cor:Jdefinable` to
`odg:cor:definablect`; `odg:eq:nA` to the residue formula in `odg:thm:finitequotients`; `odg:eq:pellmod8`
to the residue assertion in `odg:lem:pellsequence`; and the dependency and
audit appendices to `odg:app:verification` and `odg:app:repo`.
These preserve navigation, not old theorem numbers or environment kinds.

## Elementary algebra correspondence

The labels in the source columns are local to those archived manuscripts.
The maintained labels resolve in [article.tex](article.tex). The dispositions
below record the elementary review; the expanded assembly may combine the
statements, as described above.

| Topic | Companion source | Maintained location and disposition |
|---|---|---|
| Rings and constant-term retraction | 02 `prop:ring`, `thm:augmentation`; 05 `thm:retraction` | `odg:prop:ring`; retain the base proof and distinguish the complex kernel `J + iJ` from `J`. |
| Degree, units, finite elements and floor | 02 `lem:units`, `prop:finite`, `thm:floor`; 05 `lem:degree`, `cor:units-B`, `prop:discrete`, `prop:floor` | `odg:lem:degree`, `odg:prop:units`, and `odg:thm:floor`, with the base's intervening discrete-order argument; agree on growth-support conventions. |
| Local Hahn workspace | 05 `lem:workspace` | New `odg:lem:workspace`; the rational span of the support union contains the input family. Later global bounds may require enlargement. |
| Ordered remainder | 02 `cor:division`; 05 `cor:division` | `odg:prop:division`; ordered division does not imply Euclidean termination. |
| Ordinary divisibility and residues | 02 `thm:congruences`; 05 `thm:divisibility` | `odg:thm:finitequotients`; depends on every support exponent being nonnegative. |
| Mixed gcd and ordinary primes | 02 `cor:mixedgcd`; 05 `cor:ordinary-primes` | New `odg:cor:mixedgcd`; `(n,x) = gcd(n,ct(x)) A` for nonzero ordinary `n`. |
| Positive-characteristic quotients and completions | 02 `thm:finitequotients` and its following completion corollary; 05 `prop:finitequotients` | `odg:cor:charideals` and following prose; inverse systems use ordinary residue rings, not sets of proper-class cosets. |
| Common divisor and idempotent kernel | 02 Section 5; 05 `lem:set-bounds`, `thm:common-divisor`, `cor:idempotent-ideal` | `odg:lem:setbounds`, `odg:thm:commondivisor`, `odg:cor:Jglobal`; retain the stronger base conclusion that no set generates `J`. Add the consequences `J/J² = 0` and `J`-adic completion `ℤ`. |
| Nilpotent-image test | 02 `cor:nilpotent` | New `odg:cor:nilpotent`; the image need not be an ideal of the whole target. |
| Clearing and common multiples | 02 Section 5 and `cor:commonmultiples`; 05 `thm:fractions` | `odg:thm:fractions` and new `odg:cor:commonmultiples`; one monomial clears every ordinary power of a set-sized family. |
| Failure of integral closure | 05 `cor:not-integrally-closed` | Add its shorter witness `√2 = (√2 ω)/ω` after `odg:prop:notnormal`; retain source 01's nonconstant witness `√(ω²+1)`. |

The additions are direct support, divisibility and ideal arguments. The
review also makes explicit that constant coefficient is not order preserving
and differs from standard part; `v = −deg` translates growth exponents to
valuation exponents. Quotients by class ideals are interpreted through their
congruence maps and ordinary representatives where available.

## Review boundary after synchronization

The elementary comparison read source 02's Sections 2–5 and source 05's
normal-form, integer-part, residue and global-support arguments through
its integral-closure corollary. The expanded article's corresponding
Sections 2–4 were compared again during synchronization, including the
new univariate, CRT, prime-adic order and general no-gcd arguments. The
universal set-sized quotient is separately styled as a cited theorem;
its foundational and sibling-source proof reconciliation remains pending.

The expanded article retains the common-workspace, mixed-gcd and nilpotent
results; common multiples are combined with projective clearing, with the
stronger `M/a^k ∈ Π` conclusion in its proof. The merge restores explicit
class-quotient conventions, completion transition maps, the integer
constant condition in `Oz_H`, and the finite-product argument for the
nilpotent test. It also corrects the incoming phrase “ring of nonpositive
valuation”: `ω + ω⁻¹` has negative valuation but violates the required
support restriction. Every supported exponent must satisfy that restriction.

The subsequent review reads the expanded Sections 5–7: retraction and
positive-existential transfer, Smith systems, constant products, decomposable
fibers, binary/Pell/conic and norm rigidity, local Euler derivations,
separated powers and unimodular Fermat. It compares the Euler, separated-power
and Fermat arguments with source 05's corresponding sections. The other
Sections 5–6 source correspondences have not yet had an exhaustive
claim-by-claim reconciliation.

The review corrects the merge's direct divisibility identity
`odg:rem:separatedidentity`: differentiating `a x^m + b y^n` without killing
`a,b` gives additional terms. The local Euler derivations kill all scalar
coefficients, including the level `c`, as required. It also extends
`odg:prop:univariate` and `odg:thm:separated` from real coefficients and `B_R`
to complex coefficients and `B_C`; the real and omnific conclusions remain
special cases. These extensions are explicitly distinguished from the
archived statements. No new standard environment is added.

Further explanations cover the full zero-row condition in Smith form, real
versus complex kernels, the Pell descent's zero case, norm polynomials
without an embedding of the number field into `No`, the sign of the Euler
rule under `t = ω⁻¹`, and the kernel of a fixed Euler functional. The Fermat
proof now spells out why ratios can lie in the Hahn field while Bézout
witnesses and nonzero divisibility quotients must lie in its
nonnegative-support subring. Its ordinary-coordinate conclusion explicitly
retains the hypothesis that all three coordinates are nonzero.

The Sections 8–9 pass compares source 01's quadratic dichotomy and
transvection proof, and its positive-bound, orthogonal, symmetric-matrix and
leading-homogeneous arguments, with the maintained text. It also compares
source 02's bounded semialgebraic and nilpotent-isometry arguments. The
polarization and orthogonal-complement construction are expanded. A new
consequence of the existing inverse formula shows that the quadratic orbit
preserves its coordinate ideal, so primitive integer starting points produce
unimodular omnific families. The definite-form argument gives finite integer
isometry groups beyond the Euclidean signed-permutation case.

The bounded-set proof now handles quantified formulas explicitly: enlarge a
set-sized real closed field to contain an existential witness, then descend
by model completeness. This uses the classical theorem only between
set-sized fields. The formula's language is specified as ordered rings;
its mathematical scope is unchanged. Empty definite levels and zero matrix
size are explicit. New examples show why symmetry is essential and why
changing polynomial generators can change their top-form obstruction.

The model-completeness input was checked against Marker, *Introduction to
Model Theory*, Theorem 3.5 and Proposition 4.1; this does not independently
verify the imported surreal normal-form or real-closedness foundations.

The Section 10 pass compares source 01's Pell residue table and five-variable
guard with source 05's four-square guard, constant-term definition and failed
induction instance. Bounds and quantifier domains are explicit. The
open-induction argument now spells out preservation of quantifier-free
truth between the workspace and full ring. The order-free induction remark
specifies its nonnegative domain and supplies a formula with witnesses in
the nonnegative semiring and no subtraction. Failure of Peano arithmetic
follows directly from this failed instance, without an additional claim
about formalizing Lagrange's theorem inside arithmetic.

The three-square input was checked against the AFP entry of Danilkin and
Chevalier; the four-square statement against the pinned Mathlib source.
Glivická–Glivický, Sections 2.1, 2.3 and Theorem 1, records the nonnegative
semiring convention and Shepherdson equivalence. These checks do not prove
the imported Hahn-field real-closedness or establish new Lean coverage.
The Section 11 pass compares source 01's polynomial lifting, Pythagorean
and rational-direction proofs, source 02's homogeneous clearing and signed
existence argument, and source 05's finite ordered specialization and arc
theorem. The rational-direction theorem now has an explicit consequence:
every primitive representative of a real projective point is an ordinary
coprime integer tuple. This follows by writing its coordinate ideal as
`s Oz` using an ordinary Bézout identity; it does not identify primitivity
and unimodularity for arbitrary omnific tuples.

The finite ordered specialization proof now derives rationality of a
minimal-support convex combination and constructs a separating functional
from a closest point, rather than invoking those steps without detail.
The arc theorem is extended from integer to real system coefficients,
because the group-algebra homomorphism fixes real scalars. Its prescribed
expressions now explicitly have real coefficients. A concrete kernel
example explains why comparisons must be requested before choosing the
map. Finite-support Bézout witnesses can be included in the combined tuple;
arbitrary witnesses are not silently assumed to have finite supports.
The reverse implication uses `t = ω` to ensure finite supports, and positive
parameters preserve the prescribed signs.

The Section 12 pass compares source 02's square-discriminant proof,
sources 01–02's initial-form test, and source 05's binomial-root and failed
lifting arguments. The monic quadratic proof now records exhaustiveness and
the repeated-root case; a nonmonic example shows why a square discriminant
still needs divisibility by twice the leading coefficient. The initial-form
discussion distinguishes a maximum candidate weight from the degree after
cancellation and treats zero-variable substitution explicitly.

The two-term root obstruction now has a finite-algebra proof from the
constant-product lemma, with source 05's binomial proof retained as a
support explanation. The expansion's support and finite convolution fibers
are justified for every positive surreal exponent, without a cofinality or
topological-limit assumption. The failed-lifting example has two simple
ordinary residue roots and no omnific lift; its discriminant proves this
without reading the full series. The omnific constant-term map is explicitly
distinguished from the finite-surreal valuation ring's standard-part map.

The original Sections 13 onward (now Sections 16 onward) still await independent proof review; the assembly's own
section map and corrections in Appendix A are inputs to that review.
Imported foundations, classical results and historical priority are separate
obligations. No broad preservation of the old statement wording or numbering
is claimed after the expansion.

Two additional Diophantine manuscripts, local 06 and 07, arrived in
`cf350b1`. Commit `0240140`, concurrent with this review, integrated them as
Sections 11–13, together with results of theirs and of the quotient report's
manuscript 13 in Section 6 and source 07's quartic
(`odg:def:rem:quarticvariant`) in Section 10. Merged with this review, the
article then had 88 pages, 104 standard statements and 228 labels; Sections 1–10
keep their section numbers, while statement numbers in Sections 6 and 10
shift. That material is outside this review. Their archives are recoverable at
`de0acc6`; their code and data are present here. The
[quotient report](../set-sized-quotients-of-omnific-integers/) has thirteen
assembled manuscripts and three further placed companions (17–19); its assembly is
recorded in its own README, and its source reconciliation is not part of
this record.

The three original verification scripts are unchanged by synchronization.
Their finite examples do not prove the new class-sized arguments or establish
full equivalence of the manuscripts. No additional Lean theorem is asserted
by this reconciliation.

## Elementary definability review: Section 11

Sources 06 and 07 were recovered from `de0acc6`:
`omnific_definability_reconstruction.zip` (`omnific_definability/article.tex`)
and `Omnific_Arithmetic_Definability.zip`
(`Omnific_Arithmetic_Definability/article.tex`). This pass compares their
nonnegative-support algebra, ideal predicate, Pell and modular arguments,
integer-defining systems, real quintic comparison and natural-number clauses
with the maintained Section 11. Source 07's quartic is read for that comparison;
the inserted Remark 10.5 and other earlier additions have not thereby received
a complete proof review.

The maximum-degree proof now spells out uniqueness of the leading product
and the absence of cancellation in polynomial evaluation. An intermediate
ring need not be closed under constant coefficient: `Z[ω + 1/2]` has exactly
`Z` as its constant elements but contains an element with constant coefficient
`1/2`. Thus the order-free system's proof uses degree and coefficient
intersection, whereas the quadratic ideal predicate additionally needs its
witness in the full positive-support ring. In `Z[ω]`, `ω` has no witness
for `x² = 2y²`; over `Z[√2] + Π`, the same equation also accepts a nonzero
constant. These examples explain both boundaries without weakening the
stated theorem.

The Pell recurrence proof now exhibits its inverse matrix and explains why
finite recurrence yields a positive return to the initial point, including
modulus one. The alternative finite-ring proof gives unique degree-one
representatives. The principal-ideal argument makes denominator clearing,
nonzero constant coefficient and the lack of an integrality assumption
explicit. The intersectivity proof completes the CRT step and notes that
its two-adic construction need not lift an arbitrarily fixed residue class.
The ordinary and Gaussian witness types are distinguished. No ordered
coefficient-field hypothesis is used in the order-free argument.

All standard statement texts and labels are unchanged. This is a source-level
proof review, not new Lean coverage. Classical imported results, historical
priority, Sections 12–13 and 16–17, and the unreviewed additions in Sections
6 and 10 remain separate obligations.

## Constant-term review: Section 12

This pass compares the maintained augmentation detector, ideal test and
number-field extension with source 07's detector, augmentation and
number-field sections, and the constant-term graph and homomorphism results
with source 06's retraction section. The source files are the same recovered
versions identified in the Section 11 record above.

Witness membership now uses `A = ε⁻¹(o)` explicitly. The only inverse is
that of the nonzero scalar `ε(a)` in the coefficient field; a certificate
in `Z × R` demonstrates the construction for a zero divisor. General
polynomial coefficients are parameters in the formula, whereas `Λ` and
`Λ_K` have integer coefficients and give parameter-free definitions.
The counterexample `Z[ω]` shows that an ambient root and integer constant
coefficients alone do not suffice without the full pullback ring.
The support argument keeps exponents in the original ordered group.

The ideal's intersection description now includes both directions and the
failure over rings containing `Q`. The graph proof gives all six witnesses
and separates uniqueness of its value from uniqueness of those witnesses.
The quartic's degree is read from its `x⁴` coefficient. The splitting has
an explicit proof and multiplication formula, so the additive direct sum
cannot be mistaken for a ring direct product. The homomorphism discussion
distinguishes preservation of existential equations from invariance of
arbitrary first-order definitions under automorphisms.

The number-field proof gives witnesses in the actual coefficient subring,
without integrality or finite-generation assumptions. A further consequence
is added to the merge's Remark 12.15: a root `r` of `Λ_K` has square one
of `p`, `q`, `pq`, all nonsquares in `K`. Its integer radicand therefore
gives a one-witness existential ideal and a six-witness existential graph
under the detector's existing hypotheses. Primality of this radicand is
unnecessary. This is a deduction from the combined arguments, not a claim
that source 07 itself stated the stronger result. The formula is chosen for
the fixed fields; no uniform polynomial over all number fields is asserted.

All standard statements and source labels are preserved. Section 13 onward
is unchanged. These are source-level proofs, still pending in Lean. The
added material in Sections 6 and 10, Sections 13 and 16–17, and remaining
imported foundations, historical priority and source reconciliation still
require review.

## Integration of fraction manuscripts and the numbering then current

Two further manuscripts on omnific fractions, local 08 and 09, were placed in
`a4dcb91` and integrated after these reviews as a new Section 15
(`odg:frac:` labels), with additions to the formalization section, a partial
answer to `odg:q:homogeneous` and five new questions. That material is outside
this review. Inserting Section 15 moved the sections that followed Section 14
by one: the passes above use the numbering current when they were made: the
families section they call 11 (in the passes before the batch-25 merge) is
Section 14, and the omnific-coefficients section they call 15 is Section 16. No label was renamed or removed.

## Reconstruction and logical consequences: Section 13

This pass compares the multiplier, real reconstruction, automorphism,
Gaussian obstruction and logical sections of source 06 with the maintained
Section 13, and compares its transfer and omitted-type clauses with source
07. The recovered source versions are those identified in the Section 11
record. Imported real closedness, MRDP and historical priority remain
separate review obligations.

The fraction presentation now gives its operations and witness domains.
The multiplier proof isolates the noncancelling translated coefficient,
and the coefficient predicate explicitly tests units, not just nonzero
multipliers. The internal-reconstruction corollary has a proof and repeats
the subsection's nontrivial-exponent hypothesis. The integer-radicand ideal
predicate from the number-field extension can be substituted unchanged,
giving the same reconstruction even when two is a square in the coefficient
subring's fraction field. The value-group proof gives its equivalence and
order relations and checks the sign convention `v = −leading exponent`.
Normal-form representatives respect the proper-class convention.

The automorphism arguments distinguish exponent substitution from squaring,
use finite coefficient convolution without continuity assumptions, and
separate named complex constants from Gaussian ring parameters. The phase
twist still obstructs a definable real axis after naming all complex
constants. Standard-part existence uses the largest remaining negative
exponent; uniqueness uses that no nonzero real is infinitesimal.

The c.e.-set proof guards the free tuple and transfers auxiliary witnesses.
Its finite-system version extends to every characteristic-zero coefficient
field by using the number-field theorem's integer predicate with `K = Q`;
this needs neither ordering nor a square root of two. The same predicate
proves non-elementarity without that root. These are combined consequences,
not claims that source 06 stated the stronger generality. The collapse
obstruction now says strictly positive cone, and the singleton `x = h`
explains its parameter restriction. The quantifier-free lower bound spells
out finite Boolean combinations and uses the coefficient predicate to
exclude quantifier elimination, without adding a square-root assumption.
Canonical polynomial syntax makes the omitted type decidable, and a degree
bound supplies an ordinary integer for each finite part.

The 143 standard statements and 310 labels are retained. Two statements
have wording clarifications: the already standing nontrivial-group
hypothesis in internal reconstruction and strict positivity in the collapse
theorem. No result numbers change. Section 14 onward is unchanged. All
these source-level arguments remain pending in Lean. Added material in
Sections 6 and 10, Sections 15 and 17–18, the new companions and remaining
foundational/source reconciliation still need review.

## Denominator ideals and the multiplier theorem: Sections 15.1–15.4

This pass compares source 08's Sections 3–5 (ordinary denominators,
denominator ideals and the representation lemma) and source 09's Sections
4–6 (ordinary denominators, lowest terms and projective specialization)
with the maintained article. Source 08 is recovered from
`5fb910f:docs/new/omnific_fractions_article.zip` and source 09 from
`5fb910f:docs/new/omnific_fractions_article (1).zip`, in each case the member
`omnific_fractions/omnific_fractions.tex`. Historical novelty and the
fixed-workspace discussion are not certified by this comparison.

The denominator calculus now proves translation and reciprocal identities
explicitly, restores translation at zero, and explains why the projective
covariance formula lands in the omnific ring even when its scalar does
not. The determinant uses `δ_g`, keeping `Δ` for discriminants. A finite
tuple has a nonzero denominator by simultaneous clearing; over an arbitrary
domain this instead requires its coordinates to belong to the fraction
field. Class ideals are handled by finite sums, not sets of class cosets.

The least-denominator argument spells out cancellation and its single use
of ordered division; it does not assume a terminating Euclidean algorithm
or obtain a Bézout identity from principality. The ordinary localization
proof gives its splitting and units and distinguishes the additive direct
sum from a ring product. The proof that algebraic surreals are real
algebraic restores source 09's finite-factorization argument. Explicit
witnesses distinguish the four rings in the displayed inclusion chain.
The real-constant computation includes zero and explains divisibility by
every nonzero ordinary integer before its no-gcd argument.

The multiplier proof tracks the inverse rescaling of a Bézout row, gives
the scalar lattice before normalization, and handles a zero retraction
kernel. Its hypothesis is illustrated by `(ω,ω)`: multiplying by `ω⁻¹`
gives an omnific vector but that scalar is outside the support ring, and
the starting pair is not unimodular there. The alternative lift specifies
the ordered-pair syzygy sum, its zero pairing and its residue. Polynomial
indeterminates are distinguished from evaluated omnific parameters.

The dichotomy proof was checked in both cases, including transport of
set-generatedness under multiplication by the nonzero denominator and
the halving argument for every common divisor. Remark 15.16 inherited an
overbroad scope from source 09: denominator-ideal equivalences now apply
only to affine points. Infinity retains its rational specialization and
unimodular presentation, but has no affine denominator ideal in this text.

All 143 standard statements and 310 labels are retained, with no
renumbering. The calculus proposition drops an unnecessary nonzero
hypothesis for translation; the scope correction is in a remark. The text
from Section 15.5 onward is unchanged. These source-level arguments remain
pending in Lean. The unreviewed added material in Sections 6 and 10,
Sections 15.5–15.12, Sections 17–18, new companions and remaining imported
foundations/source reconciliation remain separate obligations.

## Rational functions, curves and dense fibers: Sections 15.5–15.7

This pass compares source 08's Sections 6–7 and source 09's Sections 7–9
with the corresponding maintained text, using the same recovered archives
as the preceding pass. The elementary-group comparison was read against
the statements and displayed matrices at `ogl:el:prop:cuspresidue` and
`ogl:el:thm:nonel` in the groups report. Its imported cusp-residue result
and the underlying amalgam proof remain a separate dependency; this pass
checks the consequences in the Diophantine article, not that entire report.

Polynomial evaluation now proves fraction-field injectivity and the
leading-degree formula for nonzero rational functions at either sign of a
purely infinite parameter. The tuple classification tracks the rescaled
denominator, nonzero multiplier and nonzero constant vector, and verifies
independence of the projective specialization from the chosen reduced
vector. Lowest terms include the attaining sign and divisibility of all
coordinates. The one-function criterion handles the zero function and
distinguishes a pole at formal zero from a zero denominator at the actual
parameter. Table entries now have explicit coprimality checks, and the
certificate procedure specifies finite ratio tests, normalization and
parameter-dependent positivity.

The local approximation proof supplies positive integer choices for both
exponents and checks the vanishing order and strict degree inequality.
A combined consequence explains the topology distinction: if
`δ = deg_ω(t) > 0`, choose `η > Nδ` for every ordinary natural `N`.
Every nonzero element of `R(t)` has leading exponent `mδ`, so its absolute
value exceeds `ω⁻η`. Thus the fixed rational-function field is discrete
in the full surreal order topology, unlike its non-discrete degree
topology. This is an explicit consequence of the earlier set-cut and
leading-degree lemmas, not a new statement attributed to the source.

The no-lcm proof identifies both inclusions in the intersection argument.
The homogeneous-system proof now uses homogeneity to justify the common
real rescaling and states the positive leading degree of a nonconstant
coordinate. The required constant vector has rational projective direction;
its entries need not themselves be rational.

The equivariance proof transports the Bézout row explicitly. The orbit
theorem now says constant real *projective* point, retaining infinity.
The ordered-field chart topology is defined, including reciprocal
neighborhoods at infinity. The focusing lemma had an undefined `1/b`
formula at the allowed value `b = 0`; the revised statement gives the
identity in that case, restricts the affine infinity image to `b ≠ 0`,
and identifies the pole `x − 1/b`. The proof checks closure under composition
and inverse, and the set-wise bound explicitly excludes the pole. The
nearby rational and irrational examples choose one focusing matrix for
both labels; their transformed column, distance and denominator are
verified. The nowhere-continuity argument covers the relative topology
at infinity as well as at affine points.

All 143 standard statements and 310 labels remain, without renumbering.
Four statement texts change: projective wording in the orbit theorem,
the zero-parameter correction in the focusing lemma, and explicit chart
topology in the dense-fiber and nowhere-continuity corollaries. Section
15.8 onward is byte-identical. The source-level results, including the
explicit topology consequence, remain pending in Lean. Sections
15.8–15.12 and 20–21 (numbered 17–18 in this pass), all of Sections 16–18, added material in Sections 6 and 10, new companions
and remaining imported foundations and source reconciliation need review.

## Localization, scale defects and Gaussian fractions: Sections 15.8–15.12

This pass compares source 08's Sections 8–13 and source 09's monomial,
workspace and Gaussian discussion with the maintained text. The archived
sources are those recovered in the preceding fraction reviews. The
sibling report's statements `osq:hd:lem:cores` and `osq:prop:fractions`
were checked for the scope comparisons; this is not a review of all
their proofs. The flatness criterion and tensor-product facts were
checked against the primary Stacks Project sources, [Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
and [Section 10.75](https://stacks.math.columbia.edu/tag/00LY), on
23 September 2026. The latter supplies the long exact sequence, symmetry
and quotient-ideal formula for Tor. The existing bibliography entry now
includes that reference.

The localization proof identifies all nonunits and the unique maximal
ideal, proves surjectivity using ordinary fractions, and explicitly
identifies its fraction field. The two-residue quotient uses ordinary
pairs as representatives without treating proper-class cosets as set
elements. The claim that the maps agree only on `ℚ` was false:
`t/(t+1)²` is a nonzero infinitesimal with both residues zero. Their
agreement locus is exactly the additive sum of `ℚ` and their joint
kernel. Both the counterexample and the decomposition have proofs and
are marked as combined consequences. A positive element with negative
rational residue now proves failure of weak order preservation; a
positive element with zero residue alone would not prove that.

Polynomial division proves the one-parameter intersection, and evaluation
at formal zero is transported explicitly to the evaluated polynomial
ring. The generator-count argument uses cardinalities of finite integer
linear combinations, without assuming the continuum hypothesis. The
enlargement proof gives a specific missing small exponent. The scale
quotient is computed as a module by cancellation and truncated polynomial
representatives. Its real dimension is `m−1`, but its module length is
infinite: the top layer contains the strictly increasing submodule chain
`ℤ ⊊ (1/2)ℤ ⊊ (1/4)ℤ ⊊ …`. This combined consequence is proved explicitly.

Integrality uses monic equations for each monomial and finite integral
adjoining; non-finiteness uses the real coefficient quotient. The
nonflatness proof computes both relation modules and the image of the
old relations after tensoring. The Tor proof presents `J ⊗ B` as the
quotient of `B²` by that image, using right exactness without assuming
injectivity on the left. The first-coordinate map gives the claimed
module isomorphism and the relation `(U,−√2 U)` gives a nonzero class.

Monomial-denominator notation now distinguishes exponents from their
coefficient-one denominators. The fixed-workspace proof gives both
localization inclusions, the rational-function field, and full coefficient
arguments for the exponential and factorial-gap examples. Gaussian
evaluation, scalar normalization, the transported Bézout row, non-set
generation and the no-gcd argument are explicit. Constant projective
directions choose a nonzero coordinate before applying the affine
denominator theorem, closing the zero-last-coordinate gap. The complex
standard part and Gaussian-rational residue have their proper names and
coordinatewise finiteness domain.

All 143 standard statements and 310 labels are retained, with unchanged
statement text and numbering. Section 16 onward is byte-identical except
for the expanded Stacks bibliography item. These arguments and the two
combined consequences remain **Pending** in Lean. The next review work
concerns Sections 17–18, added material in Sections 6 and 10, companions,
imported foundations and remaining source reconciliation.

## Integration of curve and differential rigidity manuscripts and current numbering

Five manuscripts on curve and differential rigidity, tagged C10–C14 after their
file prefixes `10-` to `14-`, were placed in `c6359e4` and integrated after the fraction manuscripts as
new Sections 16–18 (`odg:cr:` labels): the squarefree and Weierstrass theorems,
the two-ring differential principle, the classification of smooth affine curves,
arithmetic fibers, projective coordinates, group varieties and boundary examples.
The same integration added pointers in Sections 6, 7 and 14, a paragraph and a
proposed module in the formalization section, the answer to `odg:q:affine` for
smooth curves, partial answers to `odg:q:search` and `odg:q:homogeneous`, and six
new questions. That material is outside every pass recorded here. Inserting Sections 16–18
moved the three sections after them by three: the omnific-coefficients section
(called 15 or 16 above) is now Section 19, the formalization section Section 20
and the questions Section 21. Statement numbers in Sections 1–15 are unchanged,
and no label was renamed or removed.

The passes above therefore use three numberings of the last three sections.
The records up to and including the Section 11 and Section 12 reviews call the
omnific-coefficients, formalization and questions sections 15, 16 and 17 (and,
before the batch-25 merge, the families section 11); the fraction-integration
record, the Section 13 review and the Sections 15.1–15.4, 15.5–15.7 and 15.8–15.12 reviews
call them 16, 17 and 18. They are now
Sections 19, 20 and 21. Sections 1–15 and their subsections, including the
Sections 15.1–15.4 reviewed above, keep their numbers.

The merge through `6f47cf9`, following the localization review `b2a8686`,
preserves all 143 earlier standard statement texts and 310 labels. The
combined article has 194 standard results and 405 labels. Its reviewed
fraction body is byte-identical to that review, and its result numbers
through Section 15 are unchanged. The combined PDF has 163 pages after
a clean three-pass build. The current inventory includes all 194 results;
the new curve material and later additions remain unreviewed and all
omnific claims remain **Pending** in Lean.

## Gaussian fibers and étale norms: the Section 6 additions

This pass compares source 07's norm theorem and degree/units proof with
source 13's Sections 8–9 and the maintained Section 6 additions. The texts
were recovered from `de0acc6:docs/new/Omnific_Arithmetic_Definability.zip`
(member `Omnific_Arithmetic_Definability/article.tex`) and
`de0acc6:docs/new/omnific_rigidity_research.zip`
(member `omnific_rigidity/article.tex`). Source 13 belongs to the sibling
quotient report; this pass covers its fiber and norm material printed here,
not its separate quotient and module theorems.

The Gaussian fiber proof now constructs its basis parameters through
coefficient functionals, checks admissible supports in both directions,
and proves parameter uniqueness. It uses no convergence of partial sums.
The exact kernel criterion retains the ordinary-point hypothesis, with
`X−Y=√2` as a counterexample if that hypothesis is omitted. A nonzero
kernel gives an injective copy of the proper-class positive-support ideal
inside each nonempty fiber; this stronger size conclusion is proved as
a combined consequence. The real kernel can be computed by stacking the
real and imaginary parts of the complex coefficient matrix. The Gaussian
kernel uses the complex matrix itself.

The étale norm proof now constructs the splitting isomorphism by a
primitive element in each field factor and the polynomial Chinese remainder
theorem. The individual maps from a product algebra into a field need not
be injective. Their combined matrix is invertible because it represents
the splitting isomorphism. The trace matrix is its transpose product,
without conjugation. Coefficient extension preserves supports and finite
convolutions; the invertible matrix then kills every positive coefficient
of the original coordinates. No assumption that the intermediate ring
is closed under constant extraction is used. The finite étale algebra
characterization was checked against the primary [Stacks Lemma 10.143.4](https://stacks.math.columbia.edu/tag/00U3)
on 23 September 2026 and added to the bibliography. The classical
primitive-element theorem remains an imported finite-algebra result.

New proved boundary examples use `Q×Q` at norm zero and the dual-number
algebra at norm one. The proof itself extends to abstract nonnegative-support
Hahn rings in every characteristic: leading-degree multiplication and
separable splitting use no characteristic-zero hypothesis. This is a
combined extension, not a claim attributed to either source and not a
change to the coefficient fields of actual omnific integers. A purely
inseparable counterexample over `F₂(s)` shows that separability cannot
be discarded: in the coefficient field containing `θ²=s`, the polynomial
pair `(1+θT,T)` has norm one and is nonconstant.

All 194 standard statement texts and 405 labels remain, without renumbering.
The arbitrary-characteristic extension and size consequence are prose
results with explicit proofs; they remain **Pending** in Lean. Section 7
onward is byte-identical except for the appended bibliography item.
This pass does not review the new curve pointer at the end of Section 6,
the added quartic in Section 10, the curve/differential part (Sections
16–18), later formalization/questions, or remaining source reconciliation.

## Integration of the logarithmic manuscript

One further manuscript on curve and differential rigidity, tagged C15 after its
file prefix `15-`, was placed in `66d7e55` and integrated as Section 18.6
(`odg:log:` labels), appended at the end of Section 18: annihilation of
logarithmic symmetric differentials on normal-crossings compactifications, the
tangent-separation criterion, descent over any coefficient ring and finite
products. The same integration added C15 to the credits of results it reproves
in Sections 16–18, corrected its normality remark in Section 17.5, and added
notes in Sections 1, 20 and 21 (a sufficient answer to the first question of
`odg:cr:q:higher` and a further rigid class for `odg:q:affine`) and in the
appendices. That material is outside every pass recorded here. No section,
statement or equation number changed, and no label was renamed or removed.

## Combined state after the Gaussian-fiber review and batch 29

The Section 6 review was committed in `85887ed` and merged with the
batch-29 logarithmic additions through `751ff27`. All 200 standard
statement texts of that incoming article and all 416 labels are preserved;
existing result numbers are unchanged. A clean three-pass build gives a
175-page combined article. Source C15 and the other curve material remain
outside the proof review above.

Commit `f879c1e` also supplies the actual omnific ring construction and the
ring/constant-term package of `odg:prop:ring`. The guide, formalization
route and repository comparisons now distinguish historical statements
about absent Lean code from this coverage. The combined two-thread Lean
build passes 4,380 jobs and the axiom audit accepts 14,672 declarations.
Other manuscript results remain pending unless individually mapped in the
ledger; this build does not verify the remaining Diophantine proofs.

## Quartic and elementary ring/Euler proof review

This pass compares source 07's Section 8 (`lem:squares`, `thm:quartic`
and `eq:F4`), recovered from the same `de0acc6` archive identified above,
with Remark 10.5 and its surrounding comparison. The maintained proof now
gives both directions for every intermediate ring with integer constant
intersection. Pell factorization is performed in the ambient real support
ring, where its factors belong even though their coefficients need not
belong to the intermediate ring. The sum-of-squares argument then forces
every coordinate to be constant. The reverse direction chooses an ordinary
Pell coordinate above the integer input's absolute value and uses the
ordinary four-square theorem. The zero exponent group is included, and
the Gaussian counterexample is retained. The comparison now correctly
notes that both four-square versions use a theorem available in Mathlib;
`Nat.sum_four_squares` was checked in the pinned source. Its classical proof
and source 07's external exposition are imported, not independently reviewed.

The pass also reviews the maintained elementary subsections 16.2–16.3:
Lemmas 16.1–16.3 and Corollary 16.4. This is a review of the assembled
proofs, not a complete comparison of sources C10–C15. The valuation-ring
proof now gives its fraction field, units, maximal ideal and residue map
explicitly. Two supporting prose assertions needed correction:

- When the exponent group is zero, the one-sided ring is the coefficient
  field and is a valuation ring. For a nonzero exponent group, choosing a
  positive exponent gives `q = ω^γ/(1+ω^γ)` with neither `q` nor `q⁻¹`
  in the nonnegative-support ring; this proves the correctly qualified claim.
- The Euler image inclusion in the positive-support ideal need not be
  proper. On `k[ω]` in characteristic zero, the derivation taking `ωⁿ`
  to `nωⁿ` has image exactly `ω k[ω]`. The text and shared notation now
  describe a support condition, not a proper inclusion.

The derivation proof uses finite coefficient convolutions, and detection
uses a rational coordinate functional on the set-sized divisible hull.
For a nonzero series `u = a ω^α(1+ε)`, the logarithmic derivative is
`λ(α) + ∂_λ ε/(1+ε)`; the remainder is in the maximal ideal. This proves
the new explicit residue identity `ct(∂_λ u/u) = λ(deg u)` and shows why
the bound for a general logarithmic derivative need not be strict. The
relative-algebraic-closedness proof now spells out its polynomial Bézout
identity before applying joint-constant detection.

All 200 standard statement texts, 416 labels and existing result numbers
are preserved. These elementary results and the new residue identity are
**Pending** in Lean. The squarefree certificate and later geometric proofs,
curve pointers, full source comparison and remaining imported foundations
still require review. The source-07 finite verifier reproduces its recorded
output exactly; that does not prove the arbitrary-support statements.

## Squarefree certificate and Weierstrass proof review

The review now covers the maintained Section 16.4: Lemma 16.5,
Theorem 16.6, Remark 16.7, Proposition 16.8, Corollaries 16.9–16.10
and Proposition 16.11, with their examples and boundary discussion.
The degree proof uses the positive-support ideal, including the corner
`m = d = 2`, and works for every ordered abelian exponent group. The
alternative unit proof and the singular polynomial families were checked
as well. No nontriviality or divisibility of the exponent group is needed.

Three standard statements needed clarification. Differential division now
specifies an ordinary integer `m ≥ 1`, so the polynomial exponent `m−1`
is defined. The cubic proposition now separates the polynomial identity
valid at every discriminant from the normalized differential requiring
`Δ₀ ≠ 0`, and states and proves the squarefreeness equivalence. The proof
obtains the unnormalized derivative identity directly from the polynomial
certificate, including at `Δ₀ = 0`. The short Weierstrass corollary now repeats
the same nonvanishing condition for its integer and Gaussian integer
specializations. The final proper-class consequence explicitly concerns
the short integral models parametrized in the preceding proposition.

The paragraph identifying the differential contraction had a factor-of-two
error. In the assembled squarefree proof, `h = Uy∂x + 2W∂y` contracts
`dx/y`, not half that form. The direct cubic proof now calls its element
`g = h/2`, the contraction of `dx/(2y)`. This was compared with source
C13's `eq:hcertificate`, `eq:elliptich` and its geometric explanation,
recovered from `c6359e4^:docs/new/omnific_differential_rigidity.zip`, member
`omnific_differential_rigidity/omnific_differential_rigidity.tex`.
C13 consistently uses the half-form;
the mismatch was in the assembly. This targeted comparison does not
constitute a full reconciliation of sources C10–C15.

The regular differential is now described on the covering opens `y ≠ 0`
and `P′(x) ≠ 0`, with respective expressions `dx/y` and `2dy/P′(x)`.
For general Weierstrass models the proof displays the invertible projective
coordinate change and explains why a repeated root over the algebraic
closure would be singular. The plane-curve derivative criterion was
checked against [Stacks, Section 53.9](https://stacks.math.columbia.edu/tag/0BYA)
and is cited; its general geometric foundations are imported. Constant
descent is performed in the ambient field before intersecting with the
integer or Gaussian integer ring. The singular-cubic proof now handles
`a = b = 0` before dividing by `a`.

All 200 standard results and 416 labels are retained. Exactly three standard
statement texts change: `odg:cr:lem:division`, `odg:cr:prop:cubic` and
`odg:cr:cor:weierstrass`; the other 197 are unchanged. Their Lean status remains **Pending**.
The two-ring principle and later geometric proofs, curve pointers and
remaining source reconciliation still require review.

The delivered C13 and C14 verifiers were rerun with SymPy 1.14.0:
12,874 and 3,440 finite assertions pass, respectively. Their reports
match the delivered records except for the Python version. These checks
cover finite identities and examples, not arbitrary Hahn supports or
the geometric theorems. The combined Lean build after merging `40a3990`
passes 4,393 jobs and audits 14,779 declarations using only `propext`,
`Classical.choice` and `Quot.sound`; this validates the incoming residue
and divisor formalizations, not the pending squarefree theorem.

## Two-ring contraction, tangent detection and inheritance

This pass reviews Section 16.5, Definitions 16.12 and 16.18 through
Proposition 16.21, completing the maintained Section 16 proof chain.
The introduction and conventions now distinguish the coefficient fields
of C11/C13's proper-rigidity theorems from those of their affine-curve
classifications, qualify nonconstant examples by a nonzero exponent
group, and distinguish the real and complex valuation rings of finite elements.
The class convention retains each theorem's stated hypotheses.

The proof now constructs the tangent functional from pullback and the
universal property of Kähler differentials. The original field derivation
is `k`-linear; the tangent derivation of a chart after base change sends
`f ⊗ a` to `a∂(f(p_L))` and kills the new scalar factor. Contractions over
the two rings agree by naturality, without an isomorphism between their
differential modules, a map between the rings, or a common affine chart.
Over the valuation ring a degree-`r` contraction lands in `m^r`. The
symmetric clause explicitly requires positive degree: the degree-zero
section `1` would be a counterexample. Symmetric evaluation descends to
the quotient symmetric power directly, without assuming that a global
symmetric section lifts to a global tensor section.

The proper-rigidity proof uses right exactness of pullback at the actual
field-valued point. The same proof applies without smoothness when the
Kähler differential sheaf is globally generated. This is recorded as a
proved manuscript consequence, not as a general rigidity assertion for
singular varieties. Constant descent needs only affine algebra generators;
it does not need a finitely generated algebra stable under derivations.
For example, if `t = ω^γ`, `γ > 0`, and `∂t = t`, then `k[t+t²]` is not
stable: `∂(t+t²) = 2(t+t²)−t`, and degree excludes `t` from that algebra.
The rational form `dT` on the projective line gives a separate example
showing why regularity at the valuation centre is essential.

The symmetric proof works for arbitrary separating data. On a smooth
projective scheme the stated tangent-detection property is equivalent
to semiampleness of the tautological quotient line bundle: detection
gives a cover of its projective bundle by nonvanishing loci of sections
of positive powers, quasi-compactness gives a finite subcover, and raising
these sections to a common positive degree gives global generation.
The empty projective bundle is included. This is a criterion for tangent
detection, not a necessary condition for rigidity. The inheritance proof
now supplies the fiber-product factorization and explains that immersion
inheritance allows singular and nonreduced subschemes.

The contraction, constant-point and symmetric proofs were compared with
C13's sections “The two-ring differential annihilation theorem” and
“Cotangent and symmetric-differential rigidity”, recovered from the archive
identified in the preceding pass. C11's `main:curves` and `main:proper`,
in `curve-and-abelian-rigidity/article.tex` from
`c6359e4^:docs/new/Curve_and_Abelian_Rigidity.zip`, were checked for their
coefficient-field scope. This is a targeted comparison, not full
reconciliation of sources C10–C15.

The following imported foundations were checked for the needed hypotheses:
[universal differentials](https://stacks.math.columbia.edu/tag/00RM),
[properness for arbitrary valuation rings](https://stacks.math.columbia.edu/tag/0BX5),
[flat cohomological base change](https://stacks.math.columbia.edu/tag/02KH),
[the quotient projective-bundle convention and locally free pushforward](https://stacks.math.columbia.edu/tag/01OA),
and [globally generated powers of an ample line bundle](https://stacks.math.columbia.edu/tag/01PR).
They are cited foundations, not independently formalized or fully re-proved
here. The new base-change reference and shared notation make the scalar
and projective conventions explicit.

Exactly one standard statement changes, `odg:cr:thm:annihilation`, by
specifying positive symmetric degree. The other 199 standard statements
and all 416 labels are preserved. All Section 16 results and the new
prose consequences remain **Pending** in Lean. Section 17's curve proofs,
Section 18, their earlier pointers and later additions remain unreviewed.
No finite verifier is claimed to validate the geometric argument.

## Smooth curves, geometric punctures and coefficient descent

This pass reviews Sections 17.1–17.2, Lemma 17.1 through Corollary 17.10,
including the intervening one-form argument. The canonical-bundle proof
now specifies closed points and finishes the passage from nonzero fiber
evaluations to global generation by Nakayama and the support of the cokernel.
The one-form proof evaluates differentials in the ambient Hahn field; it
does not assume that Euler derivations preserve the embedded curve function
field. The puncture lemma explicitly uses a finite set of closed points.

The real-circle sentence incorrectly attached C13's full descent argument
to its affine-line-form subcase. The projective circle has two conjugate
geometric boundary points, `[1:i:0]` and `[1:-i:0]`. Its complexification is
a projective line minus two points, so the puncture lemma and coefficient
descent imply rigidity. A form of the affine line instead has just one
geometric boundary point, which is rational over the perfect coefficient
field. The hyperbola example now distinguishes all constant Hahn-support-ring
points `(c,c⁻¹)` from the two points with real omnific integer coordinates.

Descent across an arbitrary extension `L/k` now uses invariance of genus
and of the degree of the finite étale boundary. It does not assume that
`L` embeds into an algebraic closure of `k`. The polynomial-arc equivalence
uses dominance and injectivity of monomial substitution. The nonzero
exponent-group hypothesis is needed for nonconstant witnesses; a zero
group gives the coefficient field itself.

The logarithmic dimension lemma explicitly assumes an integral curve and
a closed point for its local parameter. Its proof explains the generator
`du` and the simple-pole coefficient. In the logarithmic rigidity proof,
the centre is closed and in fact lies on the boundary: a centre in the
affine curve would put every coordinate in both support rings and hence
in `k`. Locality sends the parameter to the maximal ideal, and the function
field embedding makes it nonzero. The logarithmic derivative need only be
in the valuation ring, not in its maximal ideal. Every nonzero polynomial
differential on the affine line has pole order at least two at infinity.
The subalgebra corollary now checks its nonzero-group prerequisite and
explains the nonnormal cusp counterexample. The final classification
separates the affine, positive-genus proper and genus-zero proper cases.

Targeted source comparison used C14's canonical and curve-classification
proofs, including `lem:formA1`, from `omnific_curve_rigidity/article.tex`
in `c6359e4^:docs/new/omnific_curve_rigidity (2).zip`; C12's geometric tools,
local logarithmic calculation and affine classification from the same member
name in `c6359e4^:docs/new/omnific_curve_rigidity (1).zip`; and C13's curve
proofs through `cor:allcurves`, from
`omnific_differential_rigidity/omnific_differential_rigidity.tex` in
`c6359e4^:docs/new/omnific_differential_rigidity.zip`. In particular, C13's
original circle paragraph refers to the full real-descent proof, so the
misleading association arose in the assembly. These comparisons do not
constitute full reconciliation of C10–C15.

The [curve compactification and affineness results](https://stacks.math.columbia.edu/tag/0A22)
and the [genus-zero characterization](https://stacks.math.columbia.edu/tag/0C6L)
were checked for the required hypotheses and cited explicitly. Riemann–Roch,
flat base change and the uniqueness of the smooth projective model remain
imported foundations. This proof review adds no Lean coverage: all results
of Sections 17.1–17.2 remain **Pending**. Arithmetic fibers in Section 17.3,
later applications, earlier curve pointers and the remaining source
reconciliation still require review.

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
completing the maintained Section 16 proof chain. Later passes cover the curve
classification in Sections 17.1–17.2 and the arithmetic fibers, polynomial
witnesses and separated-model descent in Section 17.3, followed by projective
coordinates and coordinate ideals in Section 17.4. The current pass covers
Section 17.5 and Sections 17.6.1–17.6.8, including the repeated-root test,
seventh-order certificate and arithmetic existence results. A further pass finishes Sections 17.6.9–17.6.10 and reviews Sections
18.1–18.4 (groups, reduced coefficients, dual numbers and sharpness).
The logarithmic pass now covers Sections 18.5–18.6 and all six standard
results there. The scope pass checks Section 20 and Sections 21.1–21.6
against the maintained statements and implementation ledger. A further
pass checks the geometric pointers in Sections 1, 6, 7 and 14 and the
statement scopes cited in Section 21.7 against the maintained neighboring
reports. Complete parallel-source reconciliation remains outside this review.
It does **not** certify integration of every result in the fifteen manuscripts
or review of all later proofs and imported classical results. Section numbers
below are those current when each pass was made; the last section gives the
present numbering. Later additions not explicitly covered and full source
reconciliation remain outside these passes. The review of Section 16
includes the two-ring principle, symmetric differentials and inheritance.
Source C16, integrated in `1ad4ad8`, adds seventeen standard results in
Section 17.6 and updates the earlier singular-curve status notes. Its
normalization criterion, conductor certificates and structural consequences
now have the targeted proof reviews below, together with its arithmetic and
repeated-root applications. Its final boundaries and audit subsections now
have a targeted consistency check against the reviewed proof and source C16.

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

## Arithmetic fibers, integer arcs and separated descent

This pass reviews Section 17.3, Theorem 17.11 through Theorem 17.17,
including the complete-fiber example. The affine models are now explicitly
closed subschemes of the displayed affine spaces, matching the sources'
equation presentations. In the exact-fiber proof each defining equation
vanishes after evaluation in the coefficient support ring and therefore
in the arithmetic subring by injectivity. No flatness of the integral
model is used. The model `2Y = 0` supplies an explicit nonflat example:
its generic fiber is a line, its characteristic-two fiber is a plane,
and its omnific fibers are still `(n+s,0)` for `s ∈ Π`.

The proof separately treats the zero exponent group. The full-class
corollary uses finite-coordinate workspaces and injective families indexed
by positive ordinals. The old sentence saying that the “whole argument”
works in one fixed workspace is now qualified: the fiber formulas and
rigidity do, but a fixed-workspace fiber is a set. It is infinite when the
group is nonzero and a singleton for the zero group. Only the full surreal
fiber has the proper-class conclusion.

The integer-arc proof writes each scaled coefficient as
`N^j c_ij = N^(j−1)(N c_ij)` and descends the defining polynomial identities
from `ℚ[S]` to `ℤ[S]`. Its inverse identity gives injectivity over domains
and, after clearing its own denominators, over every `ℤ`-torsion-free
algebra. Characteristic zero alone is insufficient: the allowed arc
`q(S)=2S` on the affine line identifies `(0,0)` and `(0,1)` in
`ℤ × 𝔽₂`. This extension and boundary example are manuscript consequences,
not additions to the standard-statement inventory or checked Lean theorems.

The congruence proof identifies its inverse and includes modulus one.
With a rational parametrization supplied, it yields either no ordinary
points or countably infinitely many, since one admissible residue class
already supplies infinitely many distinct parameters. The constructed
integer arc parametrizes the entire purely infinite fiber, not just a
subfamily: multiplication by its clearing integer `N` is a bijection of
`Π`, so `p(t₀+s) = q(s/N)`. Consequently a finite-support witness in the
same fiber can be chosen with coordinates in `ℤ[ω^γ]` for one `γ > 0`.
These conclusions concern the exceptional affine-line branch, not an
algorithm for arbitrary curves or a finite-support representation of the
original point.

The polynomial-witness proof explicitly translates the real parameter to
put the ordinary point at zero. The separated-model proof distinguishes
the ordinary point from its constant extension, spells out the closed
equalizer's zero ideal under the injective field map, and explains class
points through workspace representatives. The
[closed-equalizer fact](https://stacks.math.columbia.edu/tag/01KM)
was checked against the separatedness hypothesis; the proof already appears
in the report's equality lemma and is made explicit again at this application.
The list of higher-dimensional rigid targets remains conditional on its
later cited theorems, whose proofs are outside this pass.

Targeted source comparison used C11's arithmetic setup and
`thm:arith-rigid`/`thm:arith-line`, from
`curve-and-abelian-rigidity/article.tex` in
`c6359e4^:docs/new/Curve_and_Abelian_Rigidity.zip`; C12's `thm:descent`,
from `omnific_curve_rigidity/article.tex` in
`c6359e4^:docs/new/omnific_curve_rigidity (1).zip`; C13's `thm:fibers`
and `cor:polywitness`, from
`omnific_differential_rigidity/omnific_differential_rigidity.tex` in
`c6359e4^:docs/new/omnific_differential_rigidity.zip`; and C14's
`lem:arcs` and `prop:congruence`, from `omnific_curve_rigidity/article.tex`
in `c6359e4^:docs/new/omnific_curve_rigidity (2).zip`. This is not full
reconciliation of the six curve sources.

All results in Section 17.3 and the added prose consequences remain
**Pending** in Lean. The projective-coordinate section, subsequent geometric
applications, earlier curve pointers and full source reconciliation remain
to be reviewed.

## Projective coordinates and the rational-point obstruction

This pass reviews Section 17.4, Theorem 17.18 through Corollary 17.22,
Example 17.23 and Remark 17.24. It distinguishes a nonzero homogeneous
tuple, an invertible coordinate ideal and a unimodular tuple. A proper
principal ideal is invertible; invertibility does not assert the unit
ideal. The coordinate-point proof explicitly identifies the generic
quotient with the given tuple and factors through the closed target by
injectivity into the ambient field. The unimodular proof explains how
the constant-term identity forces the remaining scalar to be one.

For the full-class coordinate-ideal theorem, the proof now chooses finitely
many `b_i` with `Σ a_i b_i = 1` and every `a_j b_i ∈ Oz`. Numerators and
denominators of the `b_i`, the original coordinates, and these products
fit into a common workspace. Their identities make the two generated
fractional ideals inverse there. Finite witnesses, not a Noetherian
hypothesis or a spectrum of a class-sized ring, justify the descent.
The Gaussian corollary explains primitive `ℤ[i]` coordinates and the
four unit factors `±1, ±i`.

The comparison with the fraction section contained a false extra claim:
“Both agree that a principal coordinate ideal means a rational point.”
On a rational curve, `[ω:1]` is already a counterexample: its coordinate
ideal is `Oz` and its constant-term specialization is the rational point
`[0:1]`, but it is not a `ℚ`-point. The earlier rational-curve theorem
tests specialization; the current theorem tests the point itself under
the rigidity hypothesis. The statements agree for constant directions.
The source-08 corollary in Section 15 already states the correct criterion;
the mistake was in this cross-section comparison, not in that corollary.
The shared notation guide also distinguishes the constant-term value
`[0:1]` from projective standard part `[1:0]` in this example.

The elliptic example now checks the point at infinity, explains that
`ω+n` and `ω/2+n` are positive for every ordinary integer `n`, and
distinguishes redundancy of `Mx` in the ideal from divisibility of `My`
by `M`. Its displayed nonunit common divisor shows why it does not answer
the primitive Fermat question. The field-point remark separates existence
of a square root from detection of a negative tail: a singular cubic can
have both coordinates in `Oz`. The explicit nonsingular binomial examples
do have the displayed negative coefficients.

The proofs were compared with C12's projective-coordinate section through
its elliptic denominator example, from `omnific_curve_rigidity/article.tex`
in `c6359e4^:docs/new/omnific_curve_rigidity (1).zip`, and C14's unimodular
coordinate theorem and rational-projective corollaries, from the same member
name in `c6359e4^:docs/new/omnific_curve_rigidity (2).zip`. The imported
[invertible-quotient description of projective space](https://stacks.math.columbia.edu/tag/01ND)
was checked for its precise generating-section hypothesis. This is targeted
source comparison, not complete reconciliation of C10–C15.

All five standard results in Section 17.4 retain their statements, and all
remain **Pending** in Lean. Singular curves in Section 17.5, Section 18,
earlier curve pointers and full source reconciliation remain to be reviewed.

## Singular normalization and conductor review

This pass covers Section 17.5 and Sections 17.6.1–17.6.5: the criterion
`odg:sg:thm:main`, its Seidenberg/conductor and finite-order lemmas, the
boundary-place and one-place arguments, positive genus, descent, scale
independence, finite birational invariance, dimension-one schemes and the
polynomial witness in each fiber (`odg:sg:cor:fibre`). These are eleven
standard results. The repeated-root applications in Section 17.6.6 onward,
Section 18, remaining classical imports and full source reconciliation
remain outside this pass.

The opening normalization discussion contained two incorrect inferences.
Failure of normality does not itself exhibit a constant-curve point with
no lift. For a nonconstant point the coordinate map is injective, so its
function field embeds in the fraction field of the Hahn support ring.
Normality in that fraction field suffices for a lift. In particular,
`𝕜[ω]` is normal; the square root of `ω²+1` lies outside `𝕜(ω)` and cannot
obstruct that lift. Its simple zeros over the algebraic closure rule out
a rational square. The higher-rank witness remains a valid non-normality
example: multiplying its reverse-well-ordered negative tail by a larger
monomial puts it in the ring. Whether every curve point lifts is a separate
question, and the later summaries now retain that distinction.

The discreteness remark incorrectly put the contracted differential in
the curve function field. The proof itself correctly uses a derivation
from that field into the larger Hahn field. The corrected remark derives
commensurability of valuations from `α(∂)=h∂u`, `h∈F`, and the chosen
`v(∂u)=v(u)=γ`. It also gives the direct higher-rank counterexample
`a=ω^(−e)`, `ω^H a^n∈𝒜` for every ordinary `n`, with `H>ne` for all
ordinary `n`: positive valuation alone gives no contradiction.

The proof now constructs the conductor from denominators of finitely many
module generators, explains the Leibniz coefficient computation and the
order-zero case of the power identity, and makes independence of the
multiplier `κ^(2ℓ+1)` from the power explicit. The one-place obstruction
has the explicit bound `n>δ/r`; the genus argument uses a uniformizer at a
rational smooth point and a derivation whose leading coefficient survives.
Descent identifies the base-changed normalization via its dense integral
open and normality. The dimension-one proof explains the minimal-prime
step and the empty scheme, and the fiber proof checks constant terms and
nonconstancy of the translated polynomial parameter.

The nonzero exponent-group convention is now explicit throughout the
singular subsection and in `odg:sg:thm:allcurves`. Without it, the displayed
equivalence fails for `Γ=0` and `X=𝔸¹`: all points are constant but the
component has affine-line normalization. No other standard statement is
changed. Finite birational invariance concerns the affine normalization;
it does not equate the different point sets or identify arbitrary
birational curves such as `𝔸¹` and `𝔾ₘ`.

The comparison used source C16's non-normality example, conductor and
boundary-place proof chain and structural consequences, from
`omnific_singular_curve_rigidity/article.tex` in
`39fe674:docs/new/omnific_singular_curve_rigidity.zip`. The source already
allows its derivation to take values outside the function field; the
stronger membership assertion arose in the merged introductory remark.
Primary checks covered [Seidenberg, Section 3, printed pages 168–169](https://msp.org/pjm/1966/16-1/pjm-v16-n1-p16-s.pdf),
the [normalization factorization property](https://stacks.math.columbia.edu/tag/035E),
[finite normalization of algebraic schemes](https://stacks.math.columbia.edu/tag/0BXR),
the [valuative criterion](https://stacks.math.columbia.edu/tag/0BX5),
[Riemann–Roch](https://stacks.math.columbia.edu/tag/0BS6), and
[the local differential of a uniformizer, Lemma 53.12.3](https://stacks.math.columbia.edu/tag/0C1B).
This is a targeted comparison, not a priority determination or a complete
verification of imported algebraic geometry. The new geometric results
remain **Pending** in Lean.


## Repeated-root, certificate and arithmetic application review

This pass covers the six standard results in Sections 17.6.6–17.6.8:
`odg:sg:thm:super`, `odg:sg:cor:hyper`, `odg:sg:thm:example`,
`odg:sg:thm:omnific`, `odg:sg:prop:arithfamily` and
`odg:sg:cor:gaussian`, together with their intervening explanations.
It compares the corresponding three application sections of C16, recovered
from the archive identified in the preceding pass. The final boundaries
and audit subsections, later geometry, remaining classical imports and
full original-source reconciliation remain outside this pass.

The maintained superelliptic theorem had lost C16's explicit assumption
that `Y^m−P(X)` is irreducible. Without it the criterion is false:
`Y²=X²` has the polynomial graphs `(T,±T)` but no odd root multiplicity.
Irreducibility is now explicit both in the setup and theorem statement.
The surrounding sentence also reversed the divisibility condition for a
power. It now proves that `P` is a `p`th power precisely when every root
multiplicity is divisible by `p`, and explains why excluding these powers
for each prime divisor of `m` is equivalent to irreducibility. The other
five statements and all existing labels are unchanged.

The local calculation uses the signed exponent `−deg P` at infinity,
rather than referring there to a finite-root multiplicity. Extracting the
unit root gives `w^m=s^a`; its gcd gives the number of branches and the
ramification index. The proof identifies the affine normalization as the
inverse image of the affine line in the projective model and supplies the
integer Bézout identity that recovers the normalization parameter in the
function field. This does not assert that negative parameter powers belong
to the coordinate ring. The quadratic corollary still treats reducible
models separately and retains the sign condition over the reals.

The pinched elliptic example now verifies finiteness, birationality and the
conductor directly. The cubic leading term determines the valuation even
at arbitrary rank. A displayed binomial summand explains why the same
multiplier `x³` clears every power of the contracted differential. At
power seven the resulting nonzero ring element has positive valuation.
The derivative count is traced through Seidenberg's identity and includes
the order-zero term; neither membership of `y=z/x` in the support ring
nor optimality of seven is asserted.

The arithmetic construction explicitly checks all defining equations,
constant coefficients, finite support and injectivity in the positive
surreal exponent. Nonconstant coefficients need not be integral. The
Gaussian proof explains why a finite normalization fiber has a complex
point and why constant extraction produces an ordinary Gaussian solution.
The real node `Y²=X²(X−1)`, normalized by
`(T²+1,T(T²+1))`, illustrates the missing real preimage at `(0,0)`:
its preimages are `±i`. This explains the limitation of the construction,
not nonexistence of every possible Hahn point in that fiber.

Primary checks used the opening Galois description in
[Kummer extensions](https://stacks.math.columbia.edu/tag/09I6) and the
characteristic-zero ramification formula in
[Riemann–Hurwitz](https://stacks.math.columbia.edu/tag/0C1B).
These targeted checks do not certify priority or independently verify all
imported algebraic geometry. The finite C16 suite is a regression check
of identities and bounded examples, not a proof of the infinite statements.
All six application results remain **Pending** in Lean.


## Group varieties, coefficient algebras and sharpness review

This pass checks Sections 17.6.9–17.6.10 against the reviewed singular-curve
proof and C16's own boundaries and audit table, then reviews all thirteen
standard results in Sections 18.1–18.4, from `odg:cr:lem:invariant` through
`odg:cr:thm:dor`. It includes the comparison with the omnific-groups report's
torus, real-unipotent, complex-torus and BCH statements. Sections 18.5–18.6,
remaining scope and provenance notes, and full source reconciliation remain
outside this pass.

The invariant-form proof now identifies the algebraic inverse translation
and explains global generation. Torus descent compares a point with its
own constant term through an injective coefficient map. The finite-splitting-
field argument supplies both directions of the tensor isomorphism using a
finite coefficient basis; it is not transferred to arbitrary coefficient
algebras. The quasi-finite proof explains the constant fiber, its finite
coordinate algebra and the factorization of its image through the constants.
No smoothness of that fiber or surjectivity of the original morphism is used.

The commutative-group proof retains characteristic zero, applies the
product theorem only to the connected affine subgroup, and writes the
mutually inverse point-group maps. The resulting splitting does not claim
an algebraic splitting of the group variety. The three Milne references
previously recorded as unchecked were located in the 2017 book: Theorem
8.27, Corollaries 14.33 and 16.15, printed pages 154, 289 and 329, with the
affine convention on page 324 and characteristic-zero convention in
Section 14(d). The statement and its generalization from real/complex
coefficients are unchanged.

For reduced coefficients the proof now writes the closed equalizer ideal
and its vanishing under every coefficient map, including the zero-ring
case. The former phrase “This is not faithful flatness” was ambiguous;
the intended claim, already explicit in C11, is that the proof does not
use a faithfully flat cover. The new example
`Σ_{n≥1} s^n ω^(1/n)` over `k[s]` has admissible support but coefficients
of unbounded polynomial degree, so it is outside the image of the natural
tensor map. Failure of that map to be surjective is not a claim that it
fails to be flat.

Dual numbers are defined explicitly as `S[T]/(T²)`. The lift proof uses
the unchanged underlying space, local derivations and gluing. The defect
proof splits the two coefficient functions, identifies tangent addition
modulo the square-zero ideal and tracks the ordinary dual-number subgroup
before taking the quotient. The elliptic tangent example checks both
smoothness and its nonconstant coefficient. These nilpotents belong to
coefficient rings, not the actual surreal field.

The characteristic-two example now explains finite coefficient incidence
before pairing the off-diagonal terms, distinguishing the exact Hahn
identity from finite truncations. The characteristic-p squarefree example
remains an affine line, whereas the characteristic-two cubic has genus one.
The discretely ordered-ring proof spells out monic division, parity of
leading exponents, absence of cancellation and the nonzero element killed
by a hypothetical unital embedding. It does not identify discrete order
with absence of infinitesimal tails.

The source comparison used C11's group, reduced-coefficient, nilpotent,
positive-characteristic and discrete-order sections in
`curve-and-abelian-rigidity/article.tex` from
`c6359e4^:docs/new/Curve_and_Abelian_Rigidity.zip`, and C13's semiabelian,
vector-kernel and characteristic-p arguments in
`omnific_differential_rigidity/omnific_differential_rigidity.tex` from
`c6359e4^:docs/new/omnific_differential_rigidity.zip`. The existing C16
archive supplies its closing scope notes. This does not reconcile all
parallel arguments in C10, C12, C14 and C15.

Primary checks covered [invariant differentials, Stacks 39.6.3](https://stacks.math.columbia.edu/tag/047I),
[Milne's 2008 abelian-variety notes, IV.6.4(b)](https://www.jmilne.org/math/CourseNotes/AV.pdf),
the three cited structure statements in [Milne's 2017 algebraic-groups book](https://www.jmilne.org/math/Books/iAG2017.pdf),
[finite zero-dimensional schemes, Stacks 33.20.2](https://stacks.math.columbia.edu/tag/06LF),
and [the tangent-space description](https://stacks.math.columbia.edu/tag/0B28).
These check the precise imported scope, not priority or every proof in the
classical foundations. The van den Dries paper remains unread and no new
comparison with it is claimed. All thirteen results remain **Pending** in Lean.


## Logarithmic differentials and arithmetic descent review

This pass reviews the boundaries in Section 18.5 and all six standard
results in Section 18.6, from `odg:log:lem:valuation` through
`odg:log:prop:products`, including the tangent-separation definition,
abstract interface and curve comparison. Their statements and hypotheses
are unchanged. Later pointers and status notes in Sections 1, 6, 7, 14,
20 and 21, and complete reconciliation of the parallel sources, remain
outside this pass.

The source comparison uses `omnific_geometric_rigidity/article.tex` from
`65775fb:docs/new/omnific_geometric_rigidity.zip`: its differential-comparison
section, tangent criterion, arithmetic descent, workspace corollary, product
stability and abstract interface. Its delivered proof audit is read as an
author-side checklist, not independent certification. The maintained text's
valuation-ring lemma is already more general than C15's Hahn instance; the
proof needs exactly its stated derivation and logarithmic-derivative bounds.

The sentence “There is no ring map between” the two series rings was false.
Constant extraction followed by inclusion gives maps in both directions.
C15 only says that no such morphism is asserted in its comparison; the
stronger denial arose in the merged exposition. The correction compares
the two given inclusions in the common field and explains why the constant
retractions do not respect them for nonzero exponent groups. No theorem is
weakened or reclassified as proved.

The simple normal-crossings coordinate module is now constructed and its
independence of component equations checked. The cited Stacks section
50.15 treats one smooth divisor and explicitly defers the normal-crossings
variant; the text no longer presents it as a direct reference for the whole
claim. The local normal-crossings definition is cited separately. The image
of the valuation ring's closed point need not be closed in the target.
For `d/dt` on `k((t))`, the form `dz/z` at `z=t` contracts to `1/t`:
this counterexample explains why preserving `k[[t]]` alone is insufficient.

The annihilation proof now distinguishes pullback from its natural image in
differentials of the source ring, uses the quotient definition of symmetric
powers, and tracks the scalar in `Π^r` and in the valuation ring. Compatibility
is checked over the common field without assuming one affine chart covers
both points. Positive symmetric degree is essential. The constancy proof
writes the affine coordinate map into the joint constants before descending
its equality; the abstract interface uses that argument without claiming to
satisfy the different ideal conditions of the earlier interface.

Arithmetic descent spells out the closed equalizer ideal. The class
corollary includes denominators, cover witnesses and gluing identities in
its finite workspace data. Finite products retain the ambient separated
finite-type hypotheses; `(ω^γ,e)` makes the quasi-finite boundary concrete.
The valuation-ring examples are formal binomial Hahn sums, not topological
limits at arbitrary rank. The `t`/`ω` translation explicitly extends the
additive character to the rational hull before negating it.

Primary checks used the [valuative criterion for properness](https://stacks.math.columbia.edu/tag/0BX5),
[log poles along one divisor](https://stacks.math.columbia.edu/tag/0FMU),
and [the local normal-crossings definition](https://stacks.math.columbia.edu/tag/0BI9).
These targeted checks do not certify every imported foundation, novelty or
priority. All six standard results remain **Pending** in Lean.


## Workspace, question-status and synthesis review

This pass checks Section 20 and Sections 21.1–21.6 against the maintained
statements, including the question-status notes, not against every original
source in parallel. All 217 standard statements, all 30 question environments
and all 471 labels are unchanged. It makes the following corrections and
clarifications to the explanatory prose.

- Restricting an Euler character from the rational hull leaves the original
  exponent support unchanged; choosing the character does not require
  enlarging the point's workspace.
- The no-GCD example needs a nonzero purely infinite element. At `Γ = 0`
  the ring is `ℤ`. At `Γ = ℤ`, the purely infinite ideal is `ω ℝ[ω]`, whose
  square is `ω² ℝ[ω]`; this explicitly refutes unrestricted transfer of the
  full-class idempotence conclusion to fixed workspaces.
- The scalar-representation theorem retains the domain, retraction and
  unimodularity hypotheses. The curve results retain their coefficient and
  geometry hypotheses and use arithmetic descent to reach omnific rings.
- Smooth rigid curves have singleton constant-term fibers; the affine-line
  case has fibers isomorphic to `Π`. The previous closing assertion that all
  smooth-curve fibers are copies of `Π` was false. Singular arithmetic fibers
  are not classified by that smooth formula.
- A product with the affine line is nonrigid when the exponent group is
  nonzero and the other factor has a coefficient-field point. If the latter
  has no point, the retraction makes both point sets empty. Thus the former
  unconditional statement was false. The earlier smooth-curve summary also
  now includes the nonzero-group and geometrically integral fiber hypotheses.
- The synthesis distinguishes a differential from its contraction against
  an Euler tangent: annihilation says the contraction vanishes. It does not
  say every global differential vanishes at the point. Primitive fraction
  presentations are unique up to an overall sign, and the definition of `Π`
  explicitly quantifies its witness.

Section 20 now describes the proved implementation in dependency order at
`38425db`, retaining the chosen-Smith-reduction hypothesis, the real/complex
kernel distinction and the separate status of undecidability and geometry.
The proposed module table is still explicitly a proposal; it now breaks
across pages with a repeated header instead of forcing a large blank area. No new Lean proof
is claimed for the scope examples or geometric results. Remaining pointers,
Section 21.7, the appendices' imported foundations and complete source
reconciliation still require review.


### Subsequent discriminant addition

The merge of `fdedce0` adds source C17 as Section 19.4 (27 standard results)
and Questions 21.31–21.40, with pointers and summary additions elsewhere.
These additions remain outside the completed proof and scope reviews above,
including their new text inside Sections 20–21.6. The five changes to existing
standard statements only add C17 to their source credits. The earlier 217
mathematical statements are preserved. The full manuscript now has 244
standard results; this count does not extend the independent review scope.
The route also records the separately checked Gaussian fiber and converse
formalizations in `4037368` and `ae0210c`.


## Geometric pointers and neighboring-statement comparison

This pass reads the geometric summaries in Sections 1, 6, 7 and 14 and
checks Section 21.7 against the currently cited statements in the other
reports, at the `39a46b7` snapshot. It is a comparison of statement scope,
not an independent proof review of every imported neighboring theorem.
All 244 standard statements and all 553 labels are unchanged.

The opening summary now retains nonzero ordinary levels for Pell/norm
rigidity, characteristic zero for the cited étale theorem, and
nondegeneracy for the indefinite quadratic unipotent corollary. It states
that an automorphism of `Oz` fixes the real numbers through its extension
to `No`. The curve summaries retain `Γ ≠ 0` for existence of nonconstant
points and geometric integrality for the classification. A model over `ℤ`
with real fiber `𝔸¹_ℝ` need not itself be `𝔸¹_ℤ`; the integer-point
hypothesis is separate. The group summary now describes the kernel on
points after choosing vector coordinates, rather than implying an
algebraic splitting of the group.

The earlier polynomial-lifting pointer now spells out the complete fiber
`φ(φ⁻¹(n) + Π)`: `φ` has real polynomial coordinates, and choosing a
monomial parameter supplies a finite-support witness without asserting
that every point has finite support. The unit argument in Section 17.2
is distinguished from the general torus argument: one nonconstant unit
suffices for an integral affine curve because its specialization forces a
nonzero prime kernel in a one-dimensional coordinate ring. Generation of
the whole coordinate ring by units is not required in this curve argument.

The neighboring-report comparison now restricts the conditional GCD input
to its rank-one bounded-support ring. It distinguishes local Euler
maps from maps out of the full class into set-sized modules, and records
the nonzero 2-divisible exponent group and characteristic-zero coefficient
field for recovery from a named dilation. The group report's updated
`ogl:alg:rem:affine` already records the curve classification. Its remaining
real singular arithmetic question is not settled by the geometric
normalization criterion; the Gaussian result has a different existence
conclusion. These points are also corrected in this report's guide.

For source C17, only the positive-degree hypothesis in its introductory
summary and the statement scopes of the canonical/rich-target comparison
were checked. The latter needs integer-valued polynomials with more inputs
in the relevant ordinary-output coset than their degree; discreteness
alone does not imply translation form. Section 19.4's proofs, the remaining
C17 summaries and questions, appendix imports and complete parallel-source
reconciliation remain pending. No new Lean coverage is asserted.

Validation: the rebuilt article has 225 pages after three passes, no
warnings, unresolved references or bad boxes, and all 1,106 prior auxiliary
label numbers are preserved. The changed explanations were visually checked.
The collection's independent index, 4,950 source references and 1,680 local
Markdown destinations pass. No Lean source or finite verification program
changes in this pass.


## Positive-exponent correction after the power-rigidity merge

The incoming formalization `365bea6` exposes a missing hypothesis in
`odg:rem:powers` (alias `odg:cor:powers`). The remark now states positive
ordinary `m,n` and a nonzero ordinary integer level. Its gcd reduction uses
positive quotient exponents, and it records the checked counterexample
`ω^0 − 0² = 1` with `gcd(0,2) = 2`. The closing sentence now limits the
separated-power theorem to `m,n ≥ 2`; exponent one admits the family
`y = x^m − c`. The question-status summary is aligned. The corrected gcd
statement and zero-exponent counterexample are proved in Lean; the coprime
separated theorem remains pending there. The remark changes, but all 244
standard theorem/lemma/proposition/corollary statements are unchanged.


## First discriminant proof review: elementary lemmas and translation

This pass reviews the maintained conventions and Sections 19.4.1–19.4.3,
from `odg:disc:lem:hahn` through `odg:disc:rem:comparison` and the following
polynomial-parameter explanation. This covers nine standard results. It
does not extend to the factor/Galois/resultant consequences in Section
19.4.4, the later étale-algebra and matrix arguments, the second proof,
C17's questions or a complete comparison against the delivered manuscript.
The delivered source and proof audits remain unchanged.

The Hahn algebraic-closedness input was checked against L'Innocente–Mantova,
[Fact 2.1.1](https://arxiv.org/html/1710.07304v5#S2.SS1): the coefficient
field is algebraically closed and the exponent group is divisible. The
proof now explains the coefficientwise Leibniz rule, valuation inequality
and detection of each nonzero exponent by a rational functional. The
embedding lemma derives preservation of the embedded finite extension by
differentiating its separable minimal polynomial, so existence and
compatibility follow from restriction of the ambient derivation.

The universal certificate now displays the polynomial clearing both root
derivative denominators. The proof retains symmetry in the roots and
homogeneity in the coefficient velocities; it does not assume that the
nonnegative-support ring is integrally closed. The vanishing argument
specifies all elementary symmetric functions with indices 1 through
`m = binomial(n,2)` and evaluates the resulting polynomial `T^m` at each
velocity. The translation proof explicitly recovers squarefreeness of the
constant-term polynomial from its unchanged discriminant.

Squarefree over the arithmetic subring now means squarefree over the
coefficient field, rather than square-divisor factorization in an arbitrary
subring. Corollaries 19.15–19.16 now require positive degree, as the main
theorem does: the polynomial 1 has no unique translation when the purely
infinite ideal is nonzero. These are the only two changed standard
statements among the article's 244. The coefficient test and parameter
explanation also retain positive degree. Remark 19.17 now uses the direct
counterexample `P = ωX² + X`: its discriminant is 1, but `ct P = X`, so
translation cannot recover its degree. The earlier `6X² + X − 1` concerns
the nonmonic quadratic denominator, not failure of translation form.

The unchanged C17 finite verifier was rerun with Python 3.13.14 and SymPy
1.14.0, with output only in scratch space. All 1,126 assertions in 13 groups
pass; its JSON agrees with the delivered record except for Python version.
That run includes later finite examples but does not establish the later
proofs or arbitrary-support theorems. All C17 results remain pending in Lean.

Validation: the article builds in three passes to 226 pages with no
warnings, unresolved references or bad boxes; all 553 labels and 1,106
auxiliary label numbers are retained. The revised proof pages were checked
visually. The incoming `33b17a0` snapshot changes no standard or principal
statement in its ten modified reports. Its central-conic formalization
was checked against `odg:cor:conics`; the full two-thread Lean build passes
4,503 jobs and audits 15,678 declarations using only the three allowed axioms.
The 33-page catalogue also builds cleanly in three passes. All 4,550 indexed
standard results across 63 reports, 5,107 source references and 1,709 local
Markdown destinations pass their checks. The index anchors were refreshed
after the incoming reciprocal notes moved source lines.


## Reciprocal-note synchronization after the discriminant review

Merged `84c6398`, which adds cross-report notes in eight reports without
changing their standard or principal statements. The new Diophantine
pointers were compared with the cited floor, formal integration, formal
fraction, quartic-collapse, exponential-fiber/decidability and uniform
real-form arithmetic statements. The congruence pointer explicitly retains
positive ordinary `n`. This is a statement-scope comparison, not a proof
review of those imported results.

The Diophantine PDF was rebuilt from both branches' merged source rather
than selecting either binary version. It now has 227 pages, with no
warnings, unresolved references or bad boxes after three passes, preserving
all 553 source labels and 1,106 auxiliary label numbers. All 244 standard
statements agree with the preceding review commit. The collection still
has 4,550 standard results in 63 reports; refreshed indexes, 5,107 source
references and 1,718 local Markdown destinations pass. This merge changes
only documentation, so the successful 4,503-job Lean build and 15,678-
declaration audit remain applicable.


## Discriminant consequences and finite étale units

This pass reviews Sections 19.4.4–19.4.5, from `odg:disc:prop:factors`
through `odg:disc:rem:etalenorm`. It adds ten standard results to the nine
covered by the first C17 pass. Monogenic/arithmetic descent, critical-point
and matrix applications, the second proof, C17's questions and full
parallel-source reconciliation remain pending. No new Lean coverage is
claimed, and the delivered audit and verification artifacts are unchanged.

The factorization proof now descends both a monic divisor and its monic
quotient. The Galois proof constructs the tensor-product embedding and
explains why its finite-dimensional domain image is the compositum;
restriction preserves the ordinary splitting field because it permutes
the roots that generate that field. The minimal-polynomial argument also
makes preservation of irreducibility explicit. Positive degree is stated
in the Galois theorem; the marked-value corollary explicitly retains the
translation theorem's setting and exhibits the nonzero polynomial it uses.

The coherent-translations theorem now states `ℓ ≥ 1`. Its proof identifies
the relative-shift polynomial as a resultant in `𝕜[T]`, checks its positive
degree, and handles the one-polynomial case. An empty family gives no
uniqueness constraint. Zero constant resultants still suffice for equality
of shifts, as the existing remark says; the theorem retains its stronger
nonzero edge hypothesis.

For finite étale algebras, the review checks the general-ring inputs in
[Stacks 00U0](https://stacks.math.columbia.edu/tag/00U0),
[00UP](https://stacks.math.columbia.edu/tag/00UP) and
[00U3](https://stacks.math.columbia.edu/tag/00U3). A new bibliography entry
makes the finite-projective step precise via
[02KB](https://stacks.math.columbia.edu/tag/02KB) and
[00NX](https://stacks.math.columbia.edu/tag/00NX), without a Noetherian
assumption. The proof explains why the nonzero algebra has positive rank,
why derivations kill idempotents and preserve every generic field factor,
and why Cayley–Hamilton for multiplication implies nilpotence of the
multiplier itself.

The constant-subalgebra proof now gives the squarefree-annihilator and
Bézout argument, uses joint injectivity of the generic maps explicitly,
and identifies the basis argument proving the tensor-product injection.
Every idempotent is an algebraic constant. These facts do not assert
surjectivity onto the augmentation fiber or full descent. The comparison
with the earlier étale norm theorem treats the zero algebra separately
and explains why a unit determinant supplies an inverse for the norm
argument's element. That comparison retains characteristic zero for C17;
the earlier norm proof's wider characteristic scope is unchanged.

Validation: only three standard statements change text (Galois positive
degree, explicit translation setting for marked values, nonempty family
for resultants). All 244 standard results, 553 labels and 1,106 auxiliary
label numbers are retained. The article and catalogue build cleanly in
three passes to 227 and 33 pages; the changed proof pages were checked
visually. The 4,602-result index, 5,159 source references and 1,723 local
Markdown destinations pass before this review record is appended. No Lean
source or finite verifier changed; this pass does not rerun the previously
passing finite suite or claim that it verifies the étale proofs.

# Reconciliation of the three Diophantine manuscripts

This record covers the elementary source comparison in Sections 1–4 of the
maintained [article](article.tex), followed by proof reviews of Sections 5–9.
It does **not** certify integration of every result in the three manuscripts
or review of all later proofs and imported classical results.

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
01, 02 and 05 more broadly into a 67-statement article. The present merge
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
Sections 10 onward still await independent proof review; the assembly's own
section map and corrections in Appendix A are inputs to that review.
Imported foundations, classical results and historical priority are separate
obligations. No broad preservation of the old statement wording or numbering
is claimed after the expansion.

Two additional Diophantine manuscripts, local 06 and 07, arrived in
`cf350b1` and remain unintegrated. Their archives are recoverable at
`de0acc6`; their code and data are present here. The
[quotient report](../set-sized-quotients-of-omnific-integers/) now has thirteen
assigned manuscripts (its base and twelve companions), and still needs its
own assembly and source reconciliation.

The three original verification scripts are unchanged by synchronization.
Their finite examples do not prove the new class-sized arguments or establish
full equivalence of the manuscripts. No additional Lean theorem is asserted
by this reconciliation.

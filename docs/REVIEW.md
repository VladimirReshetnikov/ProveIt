# Exposition and proof review record

This records the scope of the September 22, 2026 documentation review. It is
separate from [Lean coverage](FORMALIZATION.md): an expanded mathematical proof,
a finite regression check and a compiled Lean theorem are different evidence.
No row below certifies every claim in an entire report.

## Reviewed portions and corrections

| Report | Inspected portion and result |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Expanded `found:thm:workspace` with arithmetic and universe-smallness prerequisites; supplied the missing positive, well-ordered control-set hypothesis in `found:prop:positive`. Distinguished intrinsic modulus/valuation topology from the full fine subspace topology. Proved the geometric convergence criterion and added `found:ex:boundedrankone`. |
| [Dynamics](surcomplex/dynamics-and-normal-forms/) | Corrected `dyn:cor:ancestry` to retain input support, proved finite dependence by word/block decompositions, and checked its arbitrary-input uses. The specialized linearizer counts an initial positive letter and retains its stronger bound. Corrected the blanket claim that changing exponent orientation reverses every inequality. |
| [Physics](physics/surreal-scalars-and-spacetime/) | Expanded `phys:prop:pole` and corrected abstract, conclusion and summaries: formal ramification preserves the pole but changes the coefficient by `w(0)^(−p)`. Distinguished the normalized recorded tests from the general theorem. |
| [Analytic geometry](surcomplex/analytic-geometry/) | Corrected `analytic:conv:notation` to define standard-part topology on finite tuples and explain its indiscrete zero-monad restriction. In `analytic:rem:fixed-not-transferred`, showed explicitly why the fixed-disk corona pair generates the whole common-domain germ ring after shrinking. |
| [Trigonometry](surcomplex/trigonometry/) | Corrected the infinitesimal-ideal notation and stated the nonzero-denominator condition in the asymptotic conventions. |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Reviewed numerical names, basic ring operations, gap extraction and inversion. Added the missing output-range filter in `lem:geom`, qualified `prop:topology` by index size, repaired the runner/build paths, and tested the candidate-cover contract with negative zero candidates. |
| [Hahn evaluation at omega](surreal/hahn-evaluation-at-omega/) | Read the main proofs through the Higman/Neumann support appendix. Corrected the false ring/semiring incomparability claim by restriction and unique extension by differences. Distinguished general infinitesimal substitution from pure-monomial exponent change; proved intrinsic Laurent-field convergence of the geometric example while retaining full-surreal nonconvergence. Expanded zero evaluation, order preservation and the root/embedding correspondence. |
| [Broadcast sums](surreal/broadcast-sum-of-surreal-sequences/) | Read the move/rank definitions, commuting truncations, number-valuedness, perturbation and nested classification proofs. Corrected `cor:cofinite` to compare families on the same index set and required an infinite index set in `cor:dyadic-tail`, with a singleton counterexample. Extended the stated constant-family theorem to arbitrary infinite index sets using its finite-exception argument. Proved the no-options criterion and clarified limit thresholds and finite normal play. |
| [Canonical forms and option graphs](surreal/canonical-forms-need-not-be-subgraphs/) | Read the finite witnesses, prefix/minimum arguments, both girth constructions, classification and ordinal examples. Proved that the first spaced-spine construction already has maximum degree three and is planar in traversal leaf order. Supplied sign and template-disjointness steps; corrected the implications between triangle-free and containment failures, stronger-containment scope, and the recorded comparison-oracle claims. |
| [Genetic gaps and primitives](surreal/genetic-gaps-and-primitives/) | Read the main article and short proof. Strengthened `thm:general` with one positive radius valid at every input, using the set of positive pairwise differences and no simultaneous choice of witnesses. Distinguished local order-field openness from the source's restricted set-union convention, and checked the cited option-construction and topology conventions against their primary texts. |
| [Exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/) | Read the displacement, valuation, lifting-obstruction, logarithmic-modulus and derivation arguments. Added a direct valuation proof of the rational-dilation obstruction while retaining the multiplication proof. Made the extra real-closedness hypothesis and nonzero logarithmic-modulus domain explicit in summaries. Verified the definition/question correspondence against the pinned KKS v3 PDF, without asserting priority or formal verification. |
| [Ordinal-support product birthdays](surreal/gonshor-product-birthdays/) | Read the sign-block, coefficient-cancellation, endpoint and inverse arguments. Expanded the cofinal squeeze at arbitrary limit ordinals and the first-differing-Cantor-coefficient argument for the two predecessor pairs. Made the finite inverse cutoff explicit and restricted the executable four-coefficient algorithm to rational inputs with decidable dyadic tests. Checked the sign rules against the pinned primary source. |
| [Laurent birthdays](surreal/gonshor-laurent-birthdays/) | Read the full mathematical dependency chain from real birthdays through finite products, infinite transfer, reciprocals and the spectrum. Corrected the pinned sign-rule citations, distinguished value birthdays from cut ranks, and specified original-prefix comparisons and successor deletion. Expanded extreme-term noncancellation, ordinal cofinal bounds and cancellation-aware finite jets; added the counterexample explaining the reciprocal's leading-exponent hypothesis. |
| [Polynomial algebra](surcomplex/polynomial-algebra/) | Read the main proofs through the multivariate residue comparison. Added nonconstant/nonzero and occupied-ball hypotheses where needed; qualified the converse from open-ball bijectivity by a nontrivial value group and supplied its singleton counterexample. Corrected the binomial support shift and quartic directions. Expanded summability indexing, zero-error lifting and the finite Nullstellensatz certificate for an arbitrary ideal; distinguished the positive-support ideal and effective-input requirements. The corrections received a second independent review. |
| [Computer algebra](foundations-and-computation/computer-algebra/) | Reviewed the main mathematical and representation contracts and compared prototype claims with their sources. Separated general Hahn residue from ordinary standard part, supplied coefficient/embedding and nonzero-polynomial hypotheses, and corrected valuation-error exponents, a geometric-tail index and constructor calls. Distinguished coordinate-significance changes from reversal of every inequality, and historical execution/package claims from current checks and Lean coverage. |
| [Gamma functions](surreal/gamma-functions/) | Read the main chain from strong substitution through tangent gaps, convexity, flatness, phase and scalar rigidity. Corrected the summary to logarithmic and relative flatness, and proved that the absolute difference at `ω` can exceed every ordinary power. Clarified positive finite arguments, monomial support, surreal-valued coefficients and finite-angle phase; added the distinct-point guard and checked the restricted-analytic transfer, Binet and remainder imports. |
| [Surquaternions](surquaternions/surquaternions/) | Read the algebra, root, support, exponential, differential and finite spectral proofs. Corrected Cayley conjugation and identified its stereographic presentation as the same chart. Supplied missing norm, sphere-divisibility and modulus-one hypotheses, the Spin(4) kernel, trivial-group topology distinctions and an integral-coefficient summability counterexample. Scoped exponential differentiation to the strongly additive BM derivation and proved the leading-commutator criterion; corrected global exponential and determinant-method claims. |
| [Finite deformations](surcomplex/finite-deformations/) | Read the main support, division, finite-algebra, residue and stability chain. Constructed the inverse in the uniform-support formal ring before establishing fine analyticity, with a second independent check. Corrected quotient-ring and residue/trace summaries, common-domain germ warnings, coordinate-power scope and the effectivity contract. Added the missing positive control-set hypothesis and Jacobian precision reasoning. |
| [Spectral theory](surcomplex/spectral-theory/) | Read the main finite geometry, variational, scale, splitting, root-field and stability proofs. Corrected the summary's Gram criterion to `2Γ`, bounded root-field sums by rank, and made Hermitian, orthogonal, zero-case and valuation-access requirements explicit. Separated principal-root extension costs from arbitrary-matrix splitting fields and exponent permission from root representation. Repaired the hypothesis ledger and trivial-group precision exception. The corrections received a second independent review. |
| [Rank-one Berkovich geometry](surcomplex/rank-one-berkovich/) | Read the main convergence, division, preparation, root-count, seminorm, annulus and entire-function arguments. Added the nonzero norm-profile hypothesis and reduction domain; expanded division uniqueness, seminorm normalization, canonical-product cancellation and the local Laurent remainder in the theta-root calculation. Checked the precise imported field, point-classification and annulus-retraction statements against primary sources. |
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/) | Read the original two-manuscript main text and finite-variable appendix before the later expansion. Strengthened the growth barrier to eventual cofinal growth, with an oscillating-range counterexample; expanded linear division, the multivariate attained-minimum argument and the preparation-only finite-zero bound. Corrected the fixed-element order-unit equivalence, nonzero-group convention and universal Bézout scope. Revised arguments received a second independent review. |
| [Global divisors](surcomplex/global-divisors/) | Read the main plane and compact proof chains through the cutoff comparison. Corrected complementary divisor support, fixed-field root-splitting scope and trivial-group reduction. Proved the coordinate-chart transfer of PID stalks and `Pic = Pic_lf`, with a second independent check. Made the genus-zero exception and workspace quantifiers explicit, proving detection by all positive cutoffs in a fixed nonzero workspace; corrected analytic-operation and source-comparison summaries. |
| [Nonabelian support](surcomplex/nonabelian-support/) | Read the full main matrix Cousin and monodromy chains. Proved that well-ordering of full raw transition support is sufficient but not necessary, while raw singular support fails both directions. Added a left-gauge counterexample; corrected matrix exp/log domains, support-condition invariance, classification scope and unsupported computation claims. The main support correction received a second review. |
| [Contours and Stokes](surcomplex/contours-and-stokes/) | Checked the revised support, smooth pullback, topology, microscopic-cycle, rational-comparison and sampling arguments. Replaced the false cofinality shortcut by finite-word incidence; corrected the word-embedding inequality and diagonal-substitution comparison. Supplied the properness and identity-theorem steps in the ramified Leray construction and expanded target composition about the ordinary map. Distinguished coefficientwise recovery from valuation limits and standard-part continuity from fine continuity. |
| [Surcomplex analysis](surcomplex/analysis/) | Read the main local-to-global arguments. Corrected fixed-point evaluation to faithfulness of function germs, proved the uniform Taylor bound with summable absolute values, and separated fine class statements from fixed-workspace assertions. Repaired root and reciprocal-support hypotheses, boundedness and function-class comparisons, and the bare-inequality Rouché counterexample. Extended the stated reciprocal-exponential value distribution to every explicit twist using a surviving cofinal family of periods; corrected kernel and branch comparisons. |

Each correction was reviewed against its local definitions and downstream uses
within the stated scope. Changed PDFs were rebuilt and affected pages inspected.
The dynamics PDF retains its three pre-existing small overfull boxes; the
evaluation-at-omega and genetic-gap PDFs retain their baseline font/layout
warnings. The revised broadcast, option-graph and automorphism PDFs have no warnings. Finite
symbolic checks support the physics examples; the corrected computability runner
passes its four separately counted suites. Its new cover regression fails when
the range filter is removed. Both option-graph suites were rerun successfully,
including all 3,860 exhaustive forms, 126 spaced-spine instances and 710
sparse/cycle certificates. Original broadcast test data were preserved without
a new run. These checks do not prove infinite statements.

Both birthday PDFs and the polynomial PDF rebuilt without warnings. The revised
computer-algebra PDF retains exactly its baseline eight underfull-box notices.
Six product-birthday example checks agree across the three existing evaluators;
the Laurent quick suite passes its 12 examples, 405 dyadic-length checks,
3 ordinal checks and 1,000 random pairs. The unchanged computer-algebra Python
suites pass separately at 69/69 and 323/323. No new Wolfram run is claimed.
Historical programs and recorded outputs for these four reports were preserved.

The Gamma, quaternion, finite-deformation and spectral PDFs also rebuilt cleanly;
the latter two remove baseline layout warnings. Gamma's 130 checks and all five
finite-deformation scripts passed on temporary copies. A separate exact
noncommutative calculation checked the quaternion differential identity through
seven homogeneous degrees. The historical quaternion and spectral suites were
not rerun for this review. Their original code and recorded outputs remain intact.

The rank-one Berkovich PDF also rebuilt without warnings, and all 542 existing
finite checks passed. Its expanded product and Laurent arguments received a
second review. The catalogue rebuilt without warnings. An independent parser
checked all 1,229 indexed theorem, lemma, proposition and corollary entries
against the 26 report sources; line hints were refreshed after the edits.

The entire-function, global-divisor and nonabelian PDFs rebuilt without warnings
or box issues; the global-divisor build removes its baseline overfull and
underfull boxes. The two entire-function suites passed 831/831 and 664/664;
the three global-divisor suites passed six check groups, 38 checks and 53/53;
the nonabelian suites passed 2,899 exact checks plus eight exact and four
numerical monodromy comparisons (maximum error `1.472e-13`, below `2e-9`).
All were run on temporary copies, preserving historical programs and data.

The contour PDF rebuilt in three passes without warnings or box issues. Its
four unchanged finite suites passed 317, 244, 167 and 632 exact checks on
temporary copies; the copied programs match the maintained historical files.
The revised passages were inspected in the 87-page PDF.

The analysis PDF rebuilt in three passes with no errors, unresolved references,
package warnings or overfull boxes. Eight underfull-box notices remain; the
baseline had six overfull boxes and six PDF-string warnings, now removed.
All nine unchanged finite programs passed on temporary copies, whose source
hashes match the maintained programs. The revised theorem passages and
catalogue entry were inspected.

## Collection-wide work

The [reader map](README.md), [catalogue](manifest.tex) and statement index
now cover all 36 canonical reports. The [notation guide](NOTATION.md) was
checked across the earlier 26-report collection; checking every convention in
the ten additions and six expanded reports remains pending. The guide records
meaningful differences rather than treating shared names as definitions:
coefficient domains, support orientation, scalar standard part versus function
reduction, topologies, strong sums, derivatives, phases and computational names.
Its report links and cited labels were checked. Maintained Markdown navigation
was checked separately from deliberately historical paths in verification records.
Original manuscript archives are accessed through Git history; their removal
from the current tree does not discharge source-claim reconciliation.

The merge of `66dd6bc` refreshed the inventory to 1,752 standard entries
across all 36 reports. An independent parser checked labels, optional titles,
counts and line hints against the merged sources. The catalogue and the three
reports with overlapping PDF changes were rebuilt from their merged LaTeX;
this checks the integration, not the new mathematical claims.

## Remaining scope

The ten reports added on September 22 and the new sections in differential
equations, dynamics, entire functions, nonabelian support, spectral theory and
exponential automorphism rigidity are outside the earlier review scopes.
Their delivered proof and source audits are inputs to review, not evidence
that this pass has checked them. Earlier validation counts above refer to
the report versions and suites then reviewed.

The reports above have received targeted corrections or a main-text reading,
as recorded in each row. Uninspected portions, imported results, source-claim
reconciliation and any formalization remain separate obligations. The
differential-equations report has unfinished edits from its review. These are
not covered by the completed-review rows above.

Continue with elementary statements and their dependencies before broad
classification theorems. For each portion, check definitions and size/domain
hypotheses, reconstruct abbreviated arguments, inspect downstream uses of any
correction, align terminology with the guide, and rebuild the affected document.
A source-to-merged-claim reconciliation is still required where a report's
provenance account alone does not establish equivalent scope.

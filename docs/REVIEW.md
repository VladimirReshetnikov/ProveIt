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
| [Differential equations](surcomplex/differential-equations/) | Reviewed the earlier scalar, finite-matrix, workspace and coherent-coordinate chains and reconciled their scope statements with the later regular-singular comparison. Corrected the domains of `Obs`, `Φ` and the normalized primitive; separated finite-system classification from Hermitian eigenvalue computation. Added the exact cocycle counterexample, expanded Dickson's lemma and the set-sized witness construction, and supplied missing coefficient, nonzero and differential-hull hypotheses. Corrected differential algebraicity, monodromy assumptions, derivative notation and stale implementation claims. A targeted follow-up corrected the Euler-stability criterion at the zero value group and the claim of unchanged derivative support. The new regular-singular and autonomous proof chains have not received a full review. |
| [Hahn-valued measures](surreal/hahn-valued-measures-and-probability/) | Read the main scalar, common-support, cylinder, product, moment, quadrature, null-ideal and coefficientwise extension proofs through conditioning. Corrected subfamily versus regrouping sums, nonnegative versus strictly positive cylinder tests, and the false leading-scalar-positivity comparison. Added an elementary coefficientwise positivity lemma and used it in boundary and mixed product constructions; expanded finite-factor reduction and the quadrature compression argument. Supplied example group and zero-case hypotheses, narrowed the near-boundary non-necessity claim, and aligned current Lean scope with the ledger. Checked the compact-interval moment citations against Schmüdgen v1 and the finite spectral references against the local report; other imported results and original-source reconciliation remain outside this review. |
| [Markov generators](surreal/markov-generators-at-every-scale/) | Read the main forest, leading-entry, remainder, stochastic-retract, realization, stability, finite-specialization and spectral proof chains and their worked examples. Corrected the nonzero workspace construction for purely real inputs and the false finite-support inference; defined the exact infinite valuation-error bound. Expanded transient-block decay, effective inversion, the real-part argument and crossover invertibility. Clarified valuations of nonzero eigenvalues, the rational-linear obstruction and the current algebraic Lean scope. A targeted follow-up supplied the discrete and one-block endpoints, strict coarsening and positive weights in the reversible converse, with explicit projection matrices and the one-state case. Checked the determinant and adjugate imports against Chebotarev–Agaev v2 with the same row orientation; other literature comparisons, priority and original-source reconciliation remain outside this review. |
| [Tail spans and differential transcendence](surreal/tail-spans-and-differential-transcendence/) | Read the coefficient-field, cofinite-span, polarization, exceptional-field, affine-plane, actual-surreal, mixed-jet, halo, approximation and undecidability proofs. Made characteristic hypotheses explicit and supplied a characteristic-two counterexample; replaced the abbreviated mixed-difference argument by finite Taylor operators, including degenerate directions. Expanded separating-functional construction, coordinate recovery and Galois splitting. Corrected the purported value-group enlargement from lexicographic integers to rationals, with the embedding specified. Aligned the partial Lean scope and rerun instructions, checked the extension-of-embeddings citation and local BM restriction, and distinguished cofinite tails from valuation prefixes. Other foundational imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Read the main support, reconstruction, sharpness, Hermite-precision and graph proofs and examples. Removed the graph theorem's divisibility assumption by auxiliary scaling and descent to the original Hahn field. Strengthened the classical uniqueness statement to arbitrary competing representations and the first-`2n−1`-moment rank obstruction, already covered in Lean. Corrected collision terminology, the measure-report comparison and stale formalization claims; checked the cited Caruso–Roe–Vaccon v1 hypotheses. A targeted follow-up restricted the equal-separation cluster formulas to at least two nodes and supplied the singleton threshold. |
| [Wick summability](surcomplex/wick-summability-certificates/) | Read the main support, semigroup, strict-alternative, diagram, connected-graph, covariance, identity and cancellation proofs and examples. Corrected the zero-semigroup boundary and proved the exact finite-sector criterion; added an integer-group counterexample explaining original-group divisibility. Extended the grouping proposition to a common nonzero complex factor and repaired the quartic comparison for signed Hahn tails. Specified monomial-insertion, zero-derivative and unit-exponent conventions and current partial Lean coverage. Checked the BM normal-form references and Etingof's normalized connected identity; other imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Read the main support, escape, orbit, recurrence, differential, generic-line, dilation, theta, torsion and mixed-operator proofs and examples. Added inward stability of strong evaluation and used it to remove divisibility from the torsion equivalence. Repaired empty refined maxima, periodic starting indices and the unit-residue period choice. Replaced the false coefficientwise coarsening picture by a valuation on the same field, with a collapsing-support example; extended the explicit witness's short cofinal proof to arbitrary tails. Checked Stanley's recurrence correspondence and the local coarsening statement; other imports, priority and original-source reconciliation remain outside this review. |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Targeted correction only: restricted the coordinate-family exact-domain clauses in all three main statements to nonzero inputs, explained the zero-input exception and aligned the README and catalogue. The rest of the main proof chains remain unreviewed in this pass. |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Targeted correction only: reconstructed the positive-definite scalar-extension proof and proved that its norm and scalar modulus exist over every ordered value group, using the even leading exponent and binomial root. Removed the false necessity of divisibility from the comparison prose, standing-hypothesis explanation and dependency table; retained the other Part I hypotheses pending review. The remaining spectral and operator proof chains have not received a main-text review. |

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

The differential-equations PDF rebuilt in three passes to 165 pages, with no
warnings, unresolved references or box issues, matching the clean baseline.
Eight earlier suites (members 01, 02 and 05–10) passed on temporary copies
at 1,395, 115, 149, 258, 291, 150, 259 and 62 checks; their program hashes
match the preserved originals. An independent exact calculation confirmed
the nonzero fourth-order coefficient in the cocycle counterexample.
Members 11 and 12 were not rerun in this review.

The Hahn-measure article and catalogue rebuilt in three passes without warnings
or box issues, at 64 and 21 pages, and the revised pages were inspected.
All three unchanged programs passed on temporary copies at 5,135, 682 and
1,009 assertions. All six copied program/build files match the preserved
originals; the historical source-15 total still includes its explicitly
identified tautological check. The new elementary positivity lemma brings
the canonical index to 1,753 standard entries; an independent parser checks
all 36 reports.

The Markov article and catalogue rebuilt without warnings or box issues, at
32 and 21 pages. The unchanged exact program passed on a temporary copy:
48 graph instances, 17,280 forests, 105 critical kernels and seven symbolic
checks. The resulting JSON matches the delivered record; historical programs,
data and source audit were preserved. The standard-statement count remains
1,753 across 36 reports.

The tail-span article and catalogue rebuilt without warnings or box issues,
at 26 and 21 pages. The unchanged verifier passed 404 checks on a temporary
copy; all check records match the delivered output, apart from Python version
and elapsed-time metadata. Historical code, data and audit files were
preserved. The index remains at 1,753 standard statements across 36 reports.

The Prony article and catalogue rebuilt without warnings or box issues, at
27 and 21 pages. The unchanged program passed 10,052 exact assertions on a
temporary copy; all output lines match the delivered record except the Python
version. Copied verification inputs are byte-identical, and historical code
and data were preserved. Statement numbering is unchanged; the independently
checked index still contains 1,753 standard statements across 36 reports.

The Wick article and catalogue rebuilt without warnings or box issues, at
32 and 21 pages, with unchanged label numbers. The unchanged verifier passed
all 7,684 cases on a temporary copy; its JSON matches the historical record
apart from elapsed time. All three copied program/build files match the
originals, and the historical data and two source audits were preserved.
The independent index still checks 1,753 standard statements in 36 reports.

The holonomic article and catalogue rebuilt at 39 and 21 pages. The two
unchanged programs passed 3,705 and 2,043 checks on temporary copies, with
outputs exactly matching the historical records; all copied inputs and the
three source audits were preserved. The new inward-stability lemma brings
the independent index to 1,754 standard statements in 36 reports.
Remote formalization work merged during this review added the escape-chain
and formal exponential-domain proofs. The merged Lean build passed 3,832
jobs and audited 5,371 declarations; the new inward and torsion proofs remain
unformalized.

The five source corrections recorded after the latest formalization survey
were checked against the report definitions and proofs. Their PDFs rebuilt in
three passes: Prony 27 pages, differential equations 165, Hahn–Tate 62,
infinite-dimensional spectral theory 54 and Markov 34. The catalogue rebuilt
at 21 pages. The Tate font-substitution warnings and the spectral report's
one underfull box match their baselines; the other four builds have no
warnings or box issues. The corrected statement, proof and summary pages
were inspected. All 1,754 statement-index entries and all maintained Markdown
links were checked. Historical code and data were preserved; these hypothesis
and proof corrections did not rerun the finite verification suites.
The full Lean build passed 3,832 jobs, including the axiom audit for 5,371
declarations. No new Lean coverage is claimed by these source corrections.

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

Of the ten reports added on September 22, Hahn-valued measures, Markov
generators, tail spans, Prony reconstruction, Wick summability and holonomic
rigidity have received the main-text reviews recorded above. The other four additions and the new sections in differential equations,
dynamics, entire functions,
nonabelian support, spectral theory and exponential automorphism rigidity
remain outside the earlier review scopes, apart from explicitly recorded
integration corrections.
Their delivered proof and source audits are inputs to review, not evidence
that this pass has checked them. Earlier validation counts above refer to
the report versions and suites then reviewed.

The reports above have received targeted corrections or a main-text reading,
as recorded in each row. Uninspected portions, imported results, source-claim
reconciliation and any formalization remain separate obligations. The
differential-equations row covers the earlier proof chains and targeted scope
corrections in the expanded report; it does not certify the two new parts.

Continue with elementary statements and their dependencies before broad
classification theorems. For each portion, check definitions and size/domain
hypotheses, reconstruct abbreviated arguments, inspect downstream uses of any
correction, align terminology with the guide, and rebuild the affected document.
A source-to-merged-claim reconciliation is still required where a report's
provenance account alone does not establish equivalent scope.

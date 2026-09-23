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
| [Differential equations](surcomplex/differential-equations/) | Reviewed the earlier scalar, finite-matrix, workspace and coherent-coordinate chains and reconciled their scope statements with the later regular-singular comparison. Corrected the domains of `Obs`, `Φ` and the normalized primitive; separated finite-system classification from Hermitian eigenvalue computation. Added the exact cocycle counterexample, expanded Dickson's lemma and the set-sized witness construction, and supplied missing coefficient, nonzero and differential-hull hypotheses. Corrected differential algebraicity, monodromy assumptions, derivative notation and stale implementation claims. A targeted follow-up corrected the Euler-stability criterion at the zero value group and the claim of unchanged derivative support. The regular-singular foundations and normalized resonant form have now been read through the finite-resonance and replacement theorems (Sections 23–24). Clarified Euler versus intrinsic differential fields and the coefficient-field hypothesis for complex morphism spaces; expanded the real-exponent word proof, finite dependency trees, empty-support cases and gauge composition. Added a nonsemisimple example explaining why whole resonant blocks are retained, and made preservation of smaller Hahn workspaces explicit. A subsequent pass read Sections 25–26: the real-monomial shear, Euler exclusion, spectral selection, real descent, both classifications, morphism and tensor dimensions, phase comparison, Hahn solutions, logarithm and forced equations. Expanded the nilpotent and residue-root arguments, distinguished morphisms in reduced and original frames, and added an explicit example of the change in classification after adjoining the logarithm. Gave a direct minimal-polynomial proof of logarithm transcendence, stated the full affine forced-solution family, and proved the degree bound sharp. The regular-singular main-text review now also covers Sections 27–28: all six examples, finite monomial adjunction, the smaller-field boundary, logarithmic counterexample and finite procedure. Expanded the rank-one equivalence proof and field-generation distinction, supplied a leading-coefficient-independent boundary comparison, and made the finite procedure require effective coefficient operations (algebraic entries suffice). Proved its reduced weight set closed under recursion, covered empty support and absent resonances, and updated the dependency table to the revised transcendence proof. The autonomous review has now begun with Section 29 and the curve setup, projective reduction and simple-zero arguments in Section 30. Expanded joint summability and composition, unit-factor uniqueness, projective chart reduction and the local Jacobian argument; made formal inverse maps zero-constant and the properness comparison set-sized. Explained genericity and parameter invariance, expanded the normalized linearizer, and supplied a quadratic formula. Checked NPT arXiv v1 Lemma 6.1(i) and Stacks Tag 0BX5 for their stated comparison roles. The multiple-zero and completeness proof in Section 30.4 has now also been read. Expanded the leading-scale argument, separated formal implicit uniqueness from uniqueness after evaluation, made logarithm-branch and coordinate changes explicit, and derived the leading difference between two values of the time parameter. Added the pure monomial family for every multiplicity and expanded the local Laurent injectivity check completing the curve classification. Section 31 has now been read: expanded the three-shift support proof, cardinality, parameter-uniform coordinate localization and scalar-to-curve reduction. Checked the BM v3 monomial inputs and NPT v1 algebraic-independence import, including its constant-field hypotheses. Corrected the README's missing nonzero-polynomial condition for derivative agreement; added the quadratic scalar example separating constant solutions from curve embeddings. Sections 32 and 33.1 have now been read. Expanded the real primitive and branch count, distinguished real and complex time constants, made the logistic family exhaustive, and corrected the logarithmic example to include its constant zero separately. Supplied the exponential family's normalized linearizer and checked the pole at infinity, giving the full solution list. Expanded contraction in an affine chart and regularity of the hyperelliptic differential at finite roots and both types of infinity; checked the constant-point distinction and both hypothesis counterexamples. The remainder of Section 33 has now been read: supplied the invariant matrix and coefficientwise integration formula for the formal logarithm, proved coordinate covariance and detailed evaluation on the entire identity monad. Expanded the global splitting, image, kernel, unique identity-monad section and basis-independent primitive criterion. Strengthened the speed threshold to every normalized derivation, since explicit primitives remove the surjectivity hypothesis, and updated all active scope notes. Checked Milne v2's algebraic-group setting, without importing analytic uniformization. Section 34 is now reviewed: strengthened the effective-input contract to include divisor and local-expansion algorithms; added the intrinsic-time example and a nonclosed invariant form on a noncommutative group. Reconciled the proposed interfaces and historical source-package claims with actual Lean finite-variable evaluation, keeping the intrinsic chain rule, inverse-map and geometric bridge obligations separate. Corrected the remaining two-surjectivity-corollary wording and checked the local Tate-report comparison. The critical-potential review now covers Sections 35–36: checked the imported ordinal tower formulas, expanded support and finite incidence, separated real powers from non-real Conway exponents, and supplied unique Wronskian coordinates and initial-stage examples. Sections 37–38 are now reviewed too: expanded the finite-primitive contradiction, generic gauge identity, Wronskian transport, Euler completeness and real descent, with an explicit critical perturbation. Corrected the power-Hahn exception at `(α,c)=(1,0)`, parameter notation and the Pinney dependency note. Sections 39–42, remaining imports and source reconciliation still require review. |
| [Hahn-valued measures](surreal/hahn-valued-measures-and-probability/) | Read the main scalar, common-support, cylinder, product, moment, quadrature, null-ideal and coefficientwise extension proofs through conditioning. Corrected subfamily versus regrouping sums, nonnegative versus strictly positive cylinder tests, and the false leading-scalar-positivity comparison. Added an elementary coefficientwise positivity lemma and used it in boundary and mixed product constructions; expanded finite-factor reduction and the quadrature compression argument. Supplied example group and zero-case hypotheses, narrowed the near-boundary non-necessity claim, and aligned current Lean scope with the ledger. Checked the compact-interval moment citations against Schmüdgen v1 and the finite spectral references against the local report; other imported results and original-source reconciliation remain outside this review. |
| [Markov generators](surreal/markov-generators-at-every-scale/) | Read the main forest, leading-entry, remainder, stochastic-retract, realization, stability, finite-specialization and spectral proof chains and their worked examples. Corrected the nonzero workspace construction for purely real inputs and the false finite-support inference; defined the exact infinite valuation-error bound. Expanded transient-block decay, effective inversion, the real-part argument and crossover invertibility. Clarified valuations of nonzero eigenvalues, the rational-linear obstruction and the current algebraic Lean scope. A targeted follow-up supplied the discrete and one-block endpoints, strict coarsening and positive weights in the reversible converse, with explicit projection matrices and the one-state case. Checked the determinant and adjugate imports against Chebotarev–Agaev v2 with the same row orientation; other literature comparisons, priority and original-source reconciliation remain outside this review. |
| [Tail spans and differential transcendence](surreal/tail-spans-and-differential-transcendence/) | Read the coefficient-field, cofinite-span, polarization, exceptional-field, affine-plane, actual-surreal, mixed-jet, halo, approximation and undecidability proofs. Made characteristic hypotheses explicit and supplied a characteristic-two counterexample; replaced the abbreviated mixed-difference argument by finite Taylor operators, including degenerate directions. Expanded separating-functional construction, coordinate recovery and Galois splitting. Corrected the purported value-group enlargement from lexicographic integers to rationals, with the embedding specified. Aligned the partial Lean scope and rerun instructions, checked the extension-of-embeddings citation and local BM restriction, and distinguished cofinite tails from valuation prefixes. Other foundational imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Read the main support, reconstruction, sharpness, Hermite-precision and graph proofs and examples. Removed the graph theorem's divisibility assumption by auxiliary scaling and descent to the original Hahn field. Strengthened the classical uniqueness statement to arbitrary competing representations and the first-`2n−1`-moment rank obstruction, already covered in Lean. Corrected collision terminology, the measure-report comparison and stale formalization claims; checked the cited Caruso–Roe–Vaccon v1 hypotheses. A targeted follow-up restricted the equal-separation cluster formulas to at least two nodes and supplied the singleton threshold. |
| [Wick summability](surcomplex/wick-summability-certificates/) | Read the main support, semigroup, strict-alternative, diagram, connected-graph, covariance, identity and cancellation proofs and examples. Corrected the zero-semigroup boundary and proved the exact finite-sector criterion; added an integer-group counterexample explaining original-group divisibility. Extended the grouping proposition to a common nonzero complex factor and repaired the quartic comparison for signed Hahn tails. Specified monomial-insertion, zero-derivative and unit-exponent conventions and current partial Lean coverage. Checked the BM normal-form references and Etingof's normalized connected identity; other imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Read the main support, escape, orbit, recurrence, differential, generic-line, dilation, theta, torsion and mixed-operator proofs and examples. Added inward stability of strong evaluation and used it to remove divisibility from the torsion equivalence. Repaired empty refined maxima, periodic starting indices and the unit-residue period choice. Replaced the false coefficientwise coarsening picture by a valuation on the same field, with a collapsing-support example; extended the explicit witness's short cofinal proof to arbitrary tails. Checked Stanley's recurrence correspondence and the local coarsening statement; other imports, priority and original-source reconciliation remain outside this review. |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Corrected the three coordinate-family exact-domain clauses to exclude zero inputs. Subsequently read Sections 2–7: support calculus, formal inverse, normalization, exact theta and coordinate domains, coarse formal evaluation, rank-one completeness, formal germs, Taylor/Hahn agreement and the first uniformization/reduction proof. Removed the unnecessary characteristic-zero restriction from the formal inverse lemma while retaining later curve hypotheses; expanded finite normalization, convexity and maximality of the infinitesimal subgroup, and the completeness tail estimate. Added the fine-positive/coarse-zero counterexample to unrestricted evaluation and aligned the two coarsenings with the notation guide. Restricted the blanket no-divisibility claim to one-period uniformization, since classification and Part II have their own extra hypotheses. Checked the complete-field hypotheses and surjective kernel statement against Tate Theorem 1, and located the Jacobi product in DLMF 20.5.9. Subsequently read the second uniformization route and Section 9: universal specialization, integral node chart, smooth and infinity inverses, constructive surjectivity, the group law, support monoids and valuation geometry. Expanded actual-point uniqueness, assembled the normalized inverse in a chart table, clarified both support inclusions, and added discrete-value and rank-two examples. Checked the universal secant identities and generic-pair lemma against Tate pp. 6–7. Read Sections 10–13: scalar extension, value and residue sequences, extension obstruction, modular recovery, negative-j classification, torsion fields and surreal transfer. Corrected the conflation of the full value quotient with its real rank-one quotient and the description of the two coarsenings. Extended modular recovery to arbitrary characteristic-zero coefficients, added a nonsplit twist example, proved torsion exhaustiveness from the kernel theorem, and expanded the degree and class-obstruction arguments. Checked BPR Remark 4.24, Poonen Corollary 4 and the stated Molcho–Wise boundedness/Tate-curve precedent. Read Sections 14–17: finite-rank coordinate reduction, positive generation, one-level and flag summability criteria, and ordinal support length. Expanded primitive-lattice quotient arguments, explicit allocation, inheritance of the inductive hypotheses, non-full lattice reduction, and the translated-coset ordinal induction. Corrected the generating-set size bound to a cardinality bound and illustrated why finite exponent fibres are essential. Checked AN Definitions 2.5 and 11.10, Theorem 8.1, Question 11.14 and its rank-one construction in the published paper. Read Sections 18–21 and the computation/limitation notes: unit robustness, Taylor summation, quasi-periodicity, minimum certificates and graph geometry, initial polynomials, implicit substitution, smooth zero lifting and examples. Expanded finite-contribution bounds, directed enumeration and the infinite-parameter recursion; added sharp cube bounds and a singular zero with nonunique lifts. Corrected the coupled zero-row equation to use the coarse reduction of the full solution, with a nonzero higher-row witness, and corrected the preserved verifier's Python-version provenance. Checked the real-valued setting and tropical minimum formula in FRSS and the formal/convergent distinction in Joswig–Smith. Remaining imports and source reconciliation are pending. |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Read the shared support tools and Part I inner-product, automatic-adjoint, defect, normal-spectrum, inverse-smooth, coercivity, completeness, duality and norm-attainment proofs. Reconstructed the norm over arbitrary value groups, then removed the unused Part I divisibility restriction after tracing every root operation. Proved closedness of the coercive range at every rank using the continuous defect projection, retaining the original metric argument under its rank-one hypothesis. Added the positive-scale guard to the backward-shift example, distinguished valuation zero from metric distance one, and aligned the two inner-product conventions, summaries and hypothesis ledger. A subsequent Part II pass read the algebra, homogeneous diagonalization, normalization, synthesis, commutant, resolvent, walk, stability, finite-section, example and transport proofs. Corrected strict diagonal-coherence claims at finite index sets and trivial groups; supplied a coherent diagonal with incoherent inverse. Distinguished vectorwise Hahn projection additivity from classical strong-operator additivity, checked against Williams Definition 5.1, and gave a rank-one counterexample to pointwise valuation convergence. Expanded the sharp boundary coefficient’s formal root-comparison step and supplied its positive-length guard. Other imported classical results, priority and source-claim reconciliation remain outside this review. |
| [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/) | Read the main support, scalar and matrix normalization, Harnack, null-ideal, functional, Fourier, quadrature, Schur, hierarchy and finite-prefix proof chains. Proved the Harnack, halo-positivity and common-kernel conclusions without divisibility by scalar normalization of quadratic forms. Expanded the zero-form and matrix-coefficient arguments; supplied the scalar-normalization positivity hypothesis and the integer-group obstruction to identity-block congruence. Corrected finite-valued versus finite-support terminology and the false disjointness of the strong and coefficientwise measure classes. Aligned partial Lean coverage and Fourier notation. Checked the classical disk representation against Bhattacharyya–Bhowmik–Kumar v3 and only the constant-kernel clause of Gesztesy–Tsekanovskii Lemma 5.3 against its preprint; other imports, priority and source-claim reconciliation remain outside this review. |
| [Expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/) | Read the main scale-ideal, inverse-branch, universal-center, fiber, periodicity, topology, extension, deformation, bounded-orbit and surreal-specialization proofs. Made degree preservation explicit in summaries and supplied a higher-degree two-cycle counterexample; clarified universal formal substitution and coefficient stabilization, and supplied the missing noncompactness argument. Distinguished an order unit from rank one, spelled out the proper-class specialization using set-sized compactness, and corrected the README’s ambiguous finite-orbit wording. Aligned partial Lean coverage and the notation guide. Checked the classical quadratic Cantor comparison and spherical Fatou/Julia definitions against Benedetto’s notes; other imports, priority and source-claim reconciliation remain separate. |

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

The Hahn–Herglotz report rebuilt at 33 pages and the catalogue at 21 pages,
both without warnings or box issues, after installing the missing TeX Gyre
font metrics and enabling their scalable font map in the build environment.
The revised theorem, proof, hypothesis, title and catalogue pages were
inspected. On a temporary copy, its unchanged verifier passed all nine suites,
including every one of the 19,683 finite null-ideal arrays (2,744 positive).
Its output matches the delivered record except for the Python version.
The five historical program, data and audit files remain byte-identical.
The full Lean build passed 3,832 jobs and the axiom audit for 5,371 declarations.
All 1,754 statement-index entries were checked after refreshing line hints.
The mathematical review does not formalize the strengthened Harnack theorem.

The expanding-polynomial dynamics report rebuilt at 32 pages and the
catalogue at 21 pages, both without warnings or box issues. The revised
title, counterexample, topology, surreal-specialization and Lean-coverage
pages were inspected. On a temporary copy, the unchanged verifier passed
38,139 exact checks; its JSON matches the delivered record except for the
Python version and elapsed time. All four historical program, build, data
and audit files remain byte-identical. The full Lean build passed 3,832 jobs
and audited 5,371 declarations. The independent statement index still
contains 1,754 entries across 36 reports; maintained Markdown links were
checked. This review adds no Lean proofs of the dynamical theorems.

The infinite-dimensional report's Part I review rebuilt the article at
53 pages and the catalogue at 21 pages. Adjusted title-page spacing brings
the status note back onto the first page, removing its otherwise empty page. The article retains its baseline
underfull box in the novelty table; there are no new warnings or box issues,
and the catalogue is clean. The revised comparison, root criterion,
closed-range proof, title, dependency table and catalogue pages were inspected.
The unchanged Part I verifier passed all 218 exact assertions in six groups
on a temporary copy using the pinned SymPy 1.14.0; its output matches the
record except for the Python version. All ten historical code, data and
provenance files remain byte-identical. The full Lean build passed 3,832 jobs
and audited 5,371 declarations. The 1,754 statement-index entries and all
maintained Markdown links were checked. This source review does not formalize
the strengthened results or validate Part II's proof chains.

The infinite-dimensional report's Part II review rebuilt the article at
54 pages, its Hahn–Herglotz companion at 33 pages and the catalogue at
22 pages. The spectral article retains its baseline novelty-table underfull
box; the companion and catalogue are clean. The revised coherence,
projection-additivity, resolvent, root-comparison, citation and companion
pages were inspected. The unchanged Part II verifier passed all 218 exact
checks on a temporary copy with SymPy 1.14.0; its JSON matches the historical
record except for the Python version. All fifteen historical code, data
and provenance files across the two reports remain byte-identical.
The statement index still checks all 1,754 entries in 36 reports, and
maintained Markdown links were checked. No Lean sources changed; the
preceding full build and axiom audit cover the unchanged library.
The Williams citation was checked only for Definition 5.1 and its
strong-operator topology footnote, not for the other imported results.

The Hahn–Tate first-route review rebuilt the article in three passes at
62 pages, with no warnings or box issues in either the baseline or revised
build. The formal-inverse, normalization, convex-subgroup, coarse-input
counterexample, completeness and classical-input pages were inspected.
On a temporary copy with SymPy 1.14.0, the unchanged source-01 verifier passed
its curve, differential, inversion, discriminant, modular-series, local-parameter,
theta and sample torsion checks; the JSON matches the delivered record
except for the Python version. All fifteen historical program, data and
audit files remain byte-identical. The independent 1,754-entry statement
index and maintained Markdown destinations were checked. No Lean sources
changed; the preceding full build and axiom audit still cover the library.
The finite checks do not certify the characteristic-free inverse lemma or
the infinite support arguments.

The Hahn–Tate second-route review rebuilt the article in three passes at
63 pages; the baseline and revised builds both had no warnings or box
issues. The smooth-chart, infinity-chart, normalized-inverse table and
valuation-example pages were inspected. The unchanged source-03 verifier
passed all 728 exact coefficient equalities through degree 12 on a temporary
copy; its JSON differs from the delivered record only in elapsed time.
All fifteen historical code, data and audit files remain byte-identical.
The independent index checked all 1,754 entries, and all 739 maintained local
Markdown destinations in 73 files resolved. The full Lean build passed
3,832 jobs and the 5,371-declaration axiom audit, using only the three allowed
axioms. The source check covered Tate's universal identities and generic-pair
lemma on pp. 6–7; it does not certify other imports or the later arithmetic
and multiscale theta sections.

The Hahn–Tate arithmetic review rebuilt the article in three passes at
64 pages and the catalogue at 22 pages, without warnings or box issues.
The value-layer, modular-recovery/twist, torsion, surreal-obstruction and
source-scope pages, and the catalogue entry, were inspected. Source 01's
unchanged verifier passed on a temporary copy with Python 3.13.14 and
SymPy 1.14.0; its JSON agrees with the historical record except for the
Python version. All fifteen historical code, data and audit files remain
byte-identical. The index checks all 1,754 entries and all 740 maintained
local Markdown destinations in 73 files resolve. The full Lean build
passed 3,832 jobs and the 5,371-declaration axiom audit using only the
allowed axioms. The primary-source check covered BPR Remark 4.24,
Poonen Corollary 4, and Molcho–Wise Definition 2.1.3.1 and Section 5.1,
including (5.1.3)–(5.1.4); it does not establish a functorial comparison
with logarithmic Picard theory or certify the other imported results.
Finite checks do not prove the arbitrary-group or class-level arguments.

The Hahn–Tate theta-foundations review rebuilt the article in three passes
at 65 pages, with no warnings or box issues; its 64-page baseline was also
clean. The allocation, lattice quotient, non-full reduction, flag and
ordinal pages were inspected. The unchanged source-02 verifier passed on
a temporary copy: 5,555 allocation cases, 1,681 irrational-shear
decompositions, 441 linear-term/minimum cases, 12 Pell witnesses and the
zero-row expansion through degree eight. Its JSON matches every field of
the historical record, and all fifteen historical code, data and audit
files remain byte-identical. These later-example checks do not mark the
later proofs as reviewed. The index checks all 1,754 entries; 740 local
Markdown destinations in 73 files resolve. The full Lean build passed
3,832 jobs and the 5,371-declaration axiom audit using only the allowed
axioms. The source comparison used the published Amini–Nicolussi article
for Definitions 2.5 and 11.10, Theorem 8.1, Question 11.14 and the adjacent
rank-one construction; it does not certify later priority or other imports.

The Hahn–Tate theta-evaluation and zero-lifting review rebuilt the article
in three passes at 65 pages without warnings or box issues. The minimum
certificate, implicit recursion, singular example, corrected coupled-zero
row and computation-provenance pages were inspected. All three unchanged
verifiers passed on temporary copies: source 01 on Python 3.13.14 with
SymPy 1.14.0, source 02 with its allocation, shear, minimum, Pell and
degree-eight zero-row checks, and source 03 with 728 coefficient equalities.
Their JSON results match the historical records except for source 01's
Python version and source 03's elapsed time. All fifteen historical code,
data and audit files remain byte-identical. The index checks all 1,754
entries; 742 local Markdown destinations in 73 files resolve. The full
Lean build passed 3,832 jobs and the 5,371-declaration axiom audit using
only the allowed axioms; no new Lean coverage is claimed. The primary-source
comparison covered Foster–Rabinoff–Shokrieh–Soto Section 1.1 and
Theorem 4.10, and Joswig–Smith Sections 2.1–2.2. It checks the scope of
those comparisons, not all imports or priority.

The differential-equations regular-singular foundations review rebuilt the
article in three passes at 166 pages, with no warnings or box issues; the
165-page baseline was also clean. The Euler gauge convention, word and
dependency-tree proofs, whole-block example, normal form and replacement
pages were inspected. Member 12's unchanged program passed all eight suites
on a temporary copy with Python 3.13.14 and SymPy 1.14.0; every JSON field
matches the delivered record. An independent exact calculation confirms the
new whole-block example's inconsistent kernel-only equation and zero
normal-form residual. All 48 historical code, data and source-log files
remain byte-identical. The index checks all 1,754 entries across 36 reports;
744 local Markdown destinations in 73 files resolve. The full Lean build
passed 3,832 jobs and the 5,371-declaration axiom audit with only the
allowed axioms. This pass reviews Sections 23–24, not the later
classification or autonomous claims, and adds no Lean coverage or
primary-source certification.

The differential-equations selection and logarithmic-repair review rebuilt
the article in three passes at 167 pages, with no warnings or box issues,
against a clean 166-page baseline. The Euler exclusion, classification,
tensor, residual-root, transcendence and forced-solution pages were
inspected. Member 12's unchanged program again passed all eight suites on
a temporary copy with Python 3.13.14 and SymPy 1.14.0; all historical JSON
fields agree. Separate exact calculations checked the two-dimensional
gauge and its endomorphisms, and the forced residual, sharp leading
coefficient and finite logarithm identity for Jordan blocks of sizes one
through six. These checks supplement the general proofs; they do not
establish the arbitrary-support statements. All 48 historical code, data
and source-log files remain byte-identical. The independent index audit
checks 1,754 entries across 36 reports; 744 local Markdown destinations
in 73 files resolve. The full Lean build passed 3,832 jobs and the
5,371-declaration audit with only the allowed axioms. This pass extends
the main-text review through Section 26; the later examples, workspace
and procedure sections, autonomous part and imported-source checks remain
separate, and no Lean coverage is added.

After this pass, synchronization merged `ebfa006` from `origin/main`,
including ten new Lean modules and their ledger mappings. The combined
state passed a fresh `LEAN_NUM_THREADS=2 lake build`: 3,872 jobs and the
5,880-declaration axiom audit, using only `propext`, `Classical.choice`
and `Quot.sound`. The independent source index still checks all 1,754
entries, and all 764 local Markdown destinations in 73 files resolve.
A wording fix in the incoming trigonometry row keeps derivative, order and
Taylor-identification claims pending, separately from the newly mapped
algebraic identities. This integration check does not widen the proof
review of the articles or independently review the new Lean mathematics.

The final regular-singular main-text pass covered differential-equations
Sections 27–28 and rebuilt the PDF in three passes at 168 pages without
warnings or box issues, against a clean 167-page baseline. The workspace,
smaller-field classification, logarithmic boundary, finite procedure and
dependency-table pages were inspected. All eight member-12 suites passed
on a temporary copy using Python 3.13.14 and SymPy 1.14.0, with every JSON
field identical to the historical result. A separate exact example used
support `{2/3,1,3/2}` and resonances `{1,2}` to check closure of the reduced
weight set and preservation of resonant data after deleting the
noncritical coefficient at `3/2`, while the gauge changes. All 48
historical code, data and source-log files remain byte-identical.
The independent index audit checks 1,754 entries across 36 reports;
765 local Markdown destinations in 73 files resolve. The full Lean build
passed 3,872 jobs and its 5,880-declaration axiom audit using only the
allowed axioms. The finite checks do not prove the infinite-support
arguments, and completion of the Part V main-text review does not certify
its remaining imported results or source reconciliation.

The first differential-equations autonomous pass covered Section 29 and
the setup, projective reduction and simple-zero arguments of Sections
30.1–30.3. The PDF rebuilt in three passes at 169 pages, without warnings
or box issues, against a clean 168-page baseline; the changed proof pages
were inspected. Member 11's unchanged verifier passed ten checks at its
default total degree four on a temporary copy with Python 3.13.14 and
SymPy 1.14.0; its output matches the historical record except for the
Python version. Separate exact calculations verified the quadratic
linearizer and both inverse identities, the inverse differential identity,
and the divided difference of `z+z²−x` with unit residue. All 48 historical
code, data and source-log files remain byte-identical. The index checks
1,754 entries across 36 reports; 766 local Markdown destinations in 73
files resolve. The full Lean build passed 3,872 jobs and the
5,880-declaration audit using only the allowed axioms. The primary-source
comparison checked NPT arXiv v1 Lemma 6.1(i) for formal simple-zero
linearization and Stacks Tag 0BX5 for the valuative properness criterion
over a set-sized field. It does not certify the multiple-zero proof,
later autonomous arguments, other imports or source reconciliation.

The second autonomous pass reviewed the multiple-zero classification and
completeness proof in Section 30.4. The report rebuilt in three passes at
170 pages without warnings or box issues, against a clean 169-page
baseline; the changed proof pages were inspected. The unchanged member-11
verifier again passed ten checks and matched the historical record except
for the Python version. Separate exact checks covered pure monomial zeros
of orders two through six, their parameter-separation coefficients, and
a triple-zero example with nonzero logarithmic residue. All 48 historical
files remain byte-identical. The full Lean build passed 3,872 jobs and
the 5,880-declaration axiom audit. These finite calculations support the
examples; they do not prove the general classification or complete its
Lean formalization. Sections 29–30 are now reviewed; later autonomous
arguments, other imports and source reconciliation remain pending.

The independent statement-index audit checks all 1,754 entries across
36 reports, and all 766 local Markdown destinations in 73 files resolve.

The third autonomous pass reviewed Section 31, including the finite-scale
field, algebraic independence, scalar-to-curve reduction and derivation
independence. The report rebuilt in three passes at 190 pages without warnings
or box issues, against a clean 189-page baseline; the changed pages were
inspected. The unchanged member-11 verifier passed all ten default-degree
checks with Python 3.13.14 and SymPy 1.14.0, matching the delivered record
apart from Python version. Separate exact checks differentiated five signed
power–logarithm–exponential monomials, checked a redundant exponential
generator, and verified the quadratic solution family and induced vector
field. All 51 historical code, data and source-log files remain byte-identical.
The full Lean build passed 3,872 jobs and its 5,880-declaration axiom audit.
BM arXiv v3 §3.2, Definition 5.1 and Remark 5.18 support the monomial inputs;
NPT arXiv v1 Lemma 7.2 and Proposition 7.3 supply the stated independence
import in a set-sized field with constant field ℂ. The bibliography now links
to those exact preprint versions. The finite checks do not prove the general
Hahn-support or classification arguments. Review of Section 32 onward and
remaining imports and source reconciliation is still pending.

The independent statement-index audit checks all 1,946 entries across
40 reports; all 804 local Markdown destinations in 87 files resolve.

The fourth autonomous pass reviewed Section 32 and Section 33.1: real
branches and all four worked equations, infinitesimal contraction, the
holomorphic-dual and hyperelliptic obstructions, branch-point constants and
both hypothesis counterexamples. The PDF rebuilt in three passes at 192
pages without warnings or box issues, against a clean 190-page baseline;
the changed pages were inspected. Member 11's unchanged verifier passed
all ten default-degree checks with Python 3.13.14 and SymPy 1.14.0; the
output matches its archive apart from Python version. Separate exact checks
covered the logistic substitution and family, the logarithmic primitive,
the normalized linearizer at −1, the pole at infinity and both obstruction
counterexamples. Six squarefree examples of degrees three through eight
verify the local infinity equations and the predicted orders of the regular
differential, including both branches in even degree. All 51 historical
code, data and source-log files remain byte-identical. The full Lean build
passed 3,872 jobs and the 5,880-declaration axiom audit. These finite checks
do not replace the general geometric and support proofs, and no new Lean
coverage is claimed. Formal-group and abelian arguments from Section 33.2
onward, the critical-potential part and remaining imports and source
reconciliation still require review.

The independent index audit checks 2,030 statement entries across all 44
current report texts; all 820 local Markdown destinations in 93 files resolve.

The final sync merged `70683e3`, including nine Lean modules from
`8924f58` for Taylor differentiation and related calculus rules. The
combined build passed 3,882 jobs and audited 5,965 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. The differential-equations
source and PDF were unchanged by that merge. The source index still checks
2,030 statements, and all 829 local Markdown destinations in 93 files
resolve. The incoming formalization mappings retain their stated scope;
they do not formalize this report's autonomous examples or obstruction.

The fifth autonomous pass reviewed Sections 33.2–33.4: the formal-group
logarithm, global splitting, abelian logarithmic-derivative image, primitive
obstruction and power-speed threshold. The latter now holds for every
normalized derivation; its explicit primitives remove the surjectivity
assumption. The PDF rebuilt in three passes at 193 pages without warnings
or box issues, against a clean 192-page baseline; the changed pages were
inspected. Member 11's unchanged verifier passed ten default-degree checks
with Python 3.13.14 and SymPy 1.14.0, matching the delivered record apart
from Python version. Separate exact checks covered the multiplicative
formal logarithm and inverse/group laws through degree six, a nonlinear
two-dimensional formal group and its invariant matrix and coordinate
covariance, homogeneous integration through degree six, and six explicit
power/logarithmic primitives. All 51 historical code, data and source-log
files remain byte-identical. Milne v2, Chapter I §1 and Theorem 6.4 were
checked for the ordinary algebraic-group setting; the formal logarithm
argument is supplied in the article and uses no analytic uniformization.
The full Lean build passed 3,882 jobs and the 5,965-declaration axiom audit.
The finite calculations support examples and formulas, not the entire
formal-group or abelian proofs. Section 34, the critical-potential part,
remaining imports and source reconciliation still require review.

The independent statement-index audit checks 2,030 entries across 44 current
texts; all 829 local Markdown destinations in 93 files resolve.

The final sync merged `4590b2c`, including the leading-term formalizations
from `6ae6fd5`. The combined Lean build passed 3,885 jobs and its
5,990-declaration audit using only `propext`, `Classical.choice` and
`Quot.sound`. The differential-equations source and PDF were unchanged by
the merge. The independent index still checks 2,030 entries, and all 833
local Markdown destinations in 93 files resolve. These incoming analytic
mappings do not formalize the abelian results reviewed here.

## Collection-wide work

The [reader map](README.md), statement index and [catalogue](manifest.tex)
now cover all 44 assembled reports, including batch 20. Their new and
expanded mathematical portions still require review. The [notation guide](NOTATION.md) was
checked across the earlier 26-report collection; checking every convention in
the fourteen additions and all expanded reports remains pending. The guide records
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

The merge from `7657737` adds batch 19 to the current index: 1,946 standard
statements across all 40 reports, with labels, headings, counts and line hints
checked independently. All 804 local Markdown destinations in 87 files resolve.
The differential-equations merge preserves the expanded multiple-zero proofs
and the upstream critical-potential part. Its PDF rebuilt in three passes at
189 pages, with no warnings or box issues, against a clean 188-page upstream
baseline; the changed proof pages were inspected. All 51 delivered code, data
and source-log files in that report remain byte-identical to the upstream
version, and the source from Part VII onward is unchanged. The combined Lean
build passes 3,872 jobs and the 5,880-declaration axiom audit. These integration
checks do not review the newly added mathematics.

The placement of `5fe7f8d`, merged during the Section 31 review's final
sync, adds four draft report sources. Their 84 standard statements are now
indexed, bringing the total to 2,030 across 44 texts. The independent parser
checks every heading, count, label and line hint; two results with only a
nested equation label are correctly indexed as unlabeled statements.
The combined Lean build again passes 3,872 jobs and the 5,880-declaration
audit. These are navigation and integration checks, not a review of the
new mathematics or completion of the incoming batch's assembly. All 820
local Markdown destinations in 93 files resolve.

The sixth autonomous pass reviewed Section 34's scope and implementation
comparisons, completing the Part VI main-text pass. It corrected the
remaining surjectivity wording, made the effective geometric input
requirements explicit, and distinguished formal time from intrinsic time.
The affine-group example explains precisely why invariant forms need not
be closed without commutativity. The ledger now maps the existing actual
finite-variable evaluation and composition prerequisites, with the
intrinsic chain rule and geometric bridge still pending.

The PDF rebuilt in three passes at 194 pages with no warnings or box issues,
against a clean 193-page baseline; the changed Section 34 pages were
inspected. Exact symbolic checks verified the translation solution, its
reciprocal projective double zero, and the affine group's left-invariant
forms and nonzero exterior derivative. These checks illustrate the scope
boundaries; they do not prove the geometric bridge or intrinsic calculus.
All 51 historical code, data and source-log files remain byte-identical.
The independent index audit checks all 2,030 statements across 44 texts,
and all 835 local Markdown destinations in 93 files resolve. The full Lean
build passed 3,885 jobs and audited 5,990 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. The critical-potential part, remaining
imports and source reconciliation remain outside this review.

The final sync merged `5ff3266`, including `3b702c9`'s closed-interval
nonnegativity proofs for actual analytic lifts. The combined Lean build
passed 3,887 jobs and audited 5,998 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. The differential-equations source and
PDF were unchanged by the merge. The independent statement audit still
checks all 2,030 entries, and all 837 local Markdown destinations in 93
files resolve. The incoming sign-lifting results retain their own scope;
they do not supply the intrinsic derivative or geometric bridge.

The first critical-potential pass reviewed Sections 35–36. It checked
ADH arXiv v3, Lemma 2.3, Proposition 2.5, Lemmas 2.6–2.8 and the derivative
formula on page 10, and pinned the bibliography link to that version.
The proof now makes the double family's well-ordered support and its at-most-two
coefficient incidence explicit, proves unique Wronskian coordinates, and
includes the empty stage and the first two normalized solution pairs.
It distinguishes sums of increments from the nonsummable family of
partial potentials, and real powers from non-real Conway exponents.

The PDF rebuilt in three passes at 195 pages without warnings or box issues,
against a clean 194-page baseline; the changed pages were inspected.
Member 13's copied verifier passed all 70 checks with Python 3.13.14 and
SymPy 1.14.0, matching its delivered output apart from Python version.
Separate exact checks covered the support order and coefficient incidence
at lengths 1–12, both initial solution pairs and their Wronskians, and the
two Cramer coordinate identities. These are finite checks, not verification
of transfinite summability or the imported intrinsic derivation. All 51
historical code, data and source-log files remain byte-identical. The full
Lean build passed 3,887 jobs and the 5,998-declaration axiom audit. The
independent source audit checks all 2,030 entries across 44 texts, and all
837 local Markdown destinations in 93 files resolve. Sections 37–42 and
the remaining imports and source reconciliation are still pending.

The final sync for the Sections 35–36 review merged `1e74537`: batch 20's
four assembled reports, measures and trigonometry expansions, catalogue
updates, and `2b323f7`'s analytic-composition and Taylor-rule uniqueness
proofs. The independent index audit checks 2,114 standard statements in
44 reports. Three stale physics line references were refreshed. The audit
also exposed five escaped-command control characters in the measures
report's new probability cross-link: repaired `\texttt`, `\tfrac` and
`\ref`, then rebuilt its 86-page PDF in three passes and inspected that
paragraph. Both the upstream baseline and repaired build have no warnings
or box issues. All other incoming article sources are unchanged by this
integration check, including the reviewed differential-equations source
and PDF. The combined Lean build passes 3,890 jobs and audits 6,044
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
All 876 local Markdown destinations in 93 files resolve. These checks
establish integration and navigation, not review of batch 20's new proofs
or Lean coverage for the critical-potential results.

The second critical-potential pass reviewed Sections 37–38. It expanded
the finite-primitive contradiction, stated the Liouville identity over an
arbitrary characteristic-zero differential field, and supplied its kernel
bijection and exact Wronskian transport. The repeated-root Jordan chain,
injective non-real factors and real descent now justify completeness
explicitly. The classification gives unique solution coefficients, the
Riccati reduction names its primitive, and an exact next-stage example
shows why a smaller perturbation can change the critical answer.

The power-Hahn comparison had an exception: `Q_{1,0} = ¼ω⁻²` belongs to
`ℂ((t^ℝ))`. The corrected support argument excludes every other potential
at stages `α ≥ 1` by a surviving exponent outside `ℝ`. Rescaled operators
retain the scale notation, the oscillator's distinct-root parameter is
explicitly positive, and the README now includes the Pinney comparison's
surjectivity and Part III import among its exceptions.

The PDF rebuilt in three passes at 195 pages, with no warnings or box
issues in either the reviewed text or its 195-page baseline; the changed
pages were inspected. The copied member-13 verifier passed all 70 checks
with Python 3.13.14 and SymPy 1.14.0 and matched the delivered output except
for Python version. Separate exact calculations checked gauge and
Wronskian transport at three scales with a variable coefficient, the
repeated-root chain, and the support exception at finite stages 1–6.
These finite checks do not verify intrinsic nonexistence or transfinite
classification. All 51 historical artifacts remain byte-identical. The
Lean build passed 3,890 jobs and audited 6,044 declarations with only the
three permitted axioms. The independent index checks 2,114 statements
across 44 reports, and all 876 local Markdown destinations in 93 files
resolve. Sections 39–42, remaining imports and source reconciliation are
still pending.

The final sync merged `63568cb`, including `49b102e`'s fine derivatives
of finite sine, cosine and the real-parameter surcomplex phase. The
combined build passed 3,893 jobs and audited 6,070 declarations using
only `propext`, `Classical.choice` and `Quot.sound`. The reviewed
critical-potential source and PDF were unchanged by the merge. All 2,114
statement-index entries still match, and all 879 local Markdown
destinations in 93 files resolve. These incoming fine-derivative proofs
do not formalize the intrinsic differential equations reviewed here.

## Remaining scope

The newly assembled [vector and tensor fields](surreal/vector-and-tensor-fields/),
[three-space](surreal/euclidean-three-space/),
[finite probability](surreal/finite-surreal-probability/) and
[field automorphisms](surcomplex/surcomplex-field-automorphisms/) reports
are now written and catalogued, but await proof review. The measures and
trigonometry expansions are also assembled; their new claims remain outside
the earlier review scopes. Delivered verification and source-audit artifacts
remain historical evidence, not a substitute for that review.

Batch 19 adds four reports whose mathematical proofs have not yet received
this review: [three duals](surcomplex/three-duals-of-hahn-vector-spaces/),
[hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/),
[transcendence over bounded support](surreal/transcendence-over-bounded-support/)
and [matrix scaling](surreal/matrix-scaling-at-surreal-scales/).
Its nonscalar dynamics, nonlinear holonomic rigidity, Drazin/Fredholm spectral
theory additions also remain pending. The critical-potential review has
now covers Sections 35–38; Sections 39–42 remain pending.
Their inclusion in the statement index does not extend an earlier proof-review
scope or establish Lean coverage.

All ten reports from the earlier September 22 integration have received the main-text proof
reviews recorded above, including both parts of infinite-dimensional
spectral theory and Sections 2–21 of Hahn–Tate uniformization. This does not
complete the imported-result and source-reconciliation work.
The expanded differential-equations report has now also received a
main-text review of the complete regular-singular part, Sections 23–28.
The autonomous pass now covers the normalized-derivation foundations, curve-realization classification, finite-scale localization, derivation independence and worked equations (Sections 29–32), plus the holomorphic-differential and hyperelliptic obstructions (Section 33.1). The formal-group and abelian proofs of Sections 33.2–33.4 are now also reviewed, including the speed threshold for every normalized derivation. Section 34's scope, input contracts and formalization comparisons have now also been reviewed, completing the Part VI main-text pass. The critical-potential review now covers Sections 35–38, including the imported tower formulas, fundamental-pair argument, Euler threshold and transfinite classification. Sections 39–42 and the remaining imports and source reconciliation still require review.
The new sections in dynamics, entire functions, nonabelian support,
spectral theory and exponential automorphism rigidity remain outside the
earlier review scopes, apart from explicitly recorded integration corrections.
Their delivered proof and source audits are inputs to review, not evidence
that this pass has checked them. Earlier validation counts above refer to
the report versions and suites then reviewed.

The reports above have received targeted corrections or a main-text reading,
as recorded in each row. Uninspected portions, imported results, source-claim
reconciliation and any formalization remain separate obligations. The
differential-equations row covers the earlier proof chains, targeted scope
corrections, and the regular-singular and autonomous main text; the
critical-potential Sections 39–42, remaining imports and source reconciliation are
still separate.

Continue with elementary statements and their dependencies before broad
classification theorems. For each portion, check definitions and size/domain
hypotheses, reconstruct abbreviated arguments, inspect downstream uses of any
correction, align terminology with the guide, and rebuild the affected document.
A source-to-merged-claim reconciliation is still required where a report's
provenance account alone does not establish equivalent scope.

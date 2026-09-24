# Exposition and proof review record

This records the scope of the September 22, 2026 documentation review. It is
separate from [Lean coverage](FORMALIZATION.md): an expanded mathematical proof,
a finite regression check and a compiled Lean theorem are different evidence.
No row below certifies every claim in an entire report.

## Reviewed portions and corrections

| Report | Inspected portion and result |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Expanded `found:thm:workspace` with arithmetic and universe-smallness prerequisites; supplied the missing positive, well-ordered control-set hypothesis in `found:prop:positive`. Distinguished intrinsic modulus/valuation topology from the full fine subspace topology. Proved the geometric convergence criterion and added `found:ex:boundedrankone`. |
| [Dynamics](surcomplex/dynamics-and-normal-forms/) | Corrected `dyn:cor:ancestry` to retain input support, proved finite dependence by word/block decompositions, and checked its arbitrary-input uses. The specialized linearizer counts an initial positive letter and retains its stronger bound. Corrected the blanket claim that changing exponent orientation reverses every inequality. The source-10 main-text review now covers Sections 7.7–7.13 and its Section 26.10 limitations: angular rank, contracted tree products, common domains, inverse ancestry, the exact criterion and examples. Expanded determinant and normal-convergence estimates, empty-support and infinite-rate cases; separated Hahn labels from integer tree weights. Corrected necessity claims about finite families and linear heights, added an exponential-height counterexample, and retained the sharp zero-rate radius at every angular rank. Checked the targeted tree-cut and inversion comparisons; other foundational/source reconciliation remains separate. |
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
| [Differential equations](surcomplex/differential-equations/) | Reviewed the earlier scalar, finite-matrix, workspace and coherent-coordinate chains and reconciled their scope statements with the later regular-singular comparison. Corrected the domains of `Obs`, `Φ` and the normalized primitive; separated finite-system classification from Hermitian eigenvalue computation. Added the exact cocycle counterexample, expanded Dickson's lemma and the set-sized witness construction, and supplied missing coefficient, nonzero and differential-hull hypotheses. Corrected differential algebraicity, monodromy assumptions, derivative notation and stale implementation claims. A targeted follow-up corrected the Euler-stability criterion at the zero value group and the claim of unchanged derivative support. The regular-singular foundations and normalized resonant form have now been read through the finite-resonance and replacement theorems (Sections 23–24). Clarified Euler versus intrinsic differential fields and the coefficient-field hypothesis for complex morphism spaces; expanded the real-exponent word proof, finite dependency trees, empty-support cases and gauge composition. Added a nonsemisimple example explaining why whole resonant blocks are retained, and made preservation of smaller Hahn workspaces explicit. A subsequent pass read Sections 25–26: the real-monomial shear, Euler exclusion, spectral selection, real descent, both classifications, morphism and tensor dimensions, phase comparison, Hahn solutions, logarithm and forced equations. Expanded the nilpotent and residue-root arguments, distinguished morphisms in reduced and original frames, and added an explicit example of the change in classification after adjoining the logarithm. Gave a direct minimal-polynomial proof of logarithm transcendence, stated the full affine forced-solution family, and proved the degree bound sharp. The regular-singular main-text review now also covers Sections 27–28: all six examples, finite monomial adjunction, the smaller-field boundary, logarithmic counterexample and finite procedure. Expanded the rank-one equivalence proof and field-generation distinction, supplied a leading-coefficient-independent boundary comparison, and made the finite procedure require effective coefficient operations (algebraic entries suffice). Proved its reduced weight set closed under recursion, covered empty support and absent resonances, and updated the dependency table to the revised transcendence proof. The autonomous review has now begun with Section 29 and the curve setup, projective reduction and simple-zero arguments in Section 30. Expanded joint summability and composition, unit-factor uniqueness, projective chart reduction and the local Jacobian argument; made formal inverse maps zero-constant and the properness comparison set-sized. Explained genericity and parameter invariance, expanded the normalized linearizer, and supplied a quadratic formula. Checked NPT arXiv v1 Lemma 6.1(i) and Stacks Tag 0BX5 for their stated comparison roles. The multiple-zero and completeness proof in Section 30.4 has now also been read. Expanded the leading-scale argument, separated formal implicit uniqueness from uniqueness after evaluation, made logarithm-branch and coordinate changes explicit, and derived the leading difference between two values of the time parameter. Added the pure monomial family for every multiplicity and expanded the local Laurent injectivity check completing the curve classification. Section 31 has now been read: expanded the three-shift support proof, cardinality, parameter-uniform coordinate localization and scalar-to-curve reduction. Checked the BM v3 monomial inputs and NPT v1 algebraic-independence import, including its constant-field hypotheses. Corrected the README's missing nonzero-polynomial condition for derivative agreement; added the quadratic scalar example separating constant solutions from curve embeddings. Sections 32 and 33.1 have now been read. Expanded the real primitive and branch count, distinguished real and complex time constants, made the logistic family exhaustive, and corrected the logarithmic example to include its constant zero separately. Supplied the exponential family's normalized linearizer and checked the pole at infinity, giving the full solution list. Expanded contraction in an affine chart and regularity of the hyperelliptic differential at finite roots and both types of infinity; checked the constant-point distinction and both hypothesis counterexamples. The remainder of Section 33 has now been read: supplied the invariant matrix and coefficientwise integration formula for the formal logarithm, proved coordinate covariance and detailed evaluation on the entire identity monad. Expanded the global splitting, image, kernel, unique identity-monad section and basis-independent primitive criterion. Strengthened the speed threshold to every normalized derivation, since explicit primitives remove the surjectivity hypothesis, and updated all active scope notes. Checked Milne v2's algebraic-group setting, without importing analytic uniformization. Section 34 is now reviewed: strengthened the effective-input contract to include divisor and local-expansion algorithms; added the intrinsic-time example and a nonclosed invariant form on a noncommutative group. Reconciled the proposed interfaces and historical source-package claims with actual Lean finite-variable evaluation, keeping the intrinsic chain rule, inverse-map and geometric bridge obligations separate. Corrected the remaining two-surjectivity-corollary wording and checked the local Tate-report comparison. The critical-potential review now covers Sections 35–36: checked the imported ordinal tower formulas, expanded support and finite incidence, separated real powers from non-real Conway exponents, and supplied unique Wronskian coordinates and initial-stage examples. Sections 37–38 are now reviewed too: expanded the finite-primitive contradiction, generic gauge identity, Wronskian transport, Euler completeness and real descent, with an explicit critical perturbation. Corrected the power-Hahn exception at `(α,c)=(1,0)`, parameter notation and the Pinney dependency note. Sections 39–40 are now reviewed: distinguished exact normal forms from earlier-scale coefficient data, defined the additive error class including the empty case, expanded inner-support bounds, derivative stability and the field-membership proof of dimensions zero, one and two. Proved failure of logarithm closure in the third field and reconciled the scope notes. Sections 41–42 are also reviewed: expanded the Galois automorphism laws, Schwarzian reconstruction and Möbius orbit, and corrected the dependency table. Remaining imports and source reconciliation still require review. |
| [Hahn-valued measures](surreal/hahn-valued-measures-and-probability/) | Read the main scalar, common-support, cylinder, product, moment, quadrature, null-ideal and coefficientwise extension proofs through conditioning. Corrected subfamily versus regrouping sums, nonnegative versus strictly positive cylinder tests, and the false leading-scalar-positivity comparison. Added an elementary coefficientwise positivity lemma and used it in boundary and mixed product constructions; expanded finite-factor reduction and the quadrature compression argument. Supplied example group and zero-case hypotheses, narrowed the near-boundary non-necessity claim, and aligned current Lean scope with the ledger. Checked the compact-interval moment citations against Schmüdgen v1 and the finite spectral references against the local report; other imported results and original-source reconciliation remain outside this review. |
| [Markov generators](surreal/markov-generators-at-every-scale/) | Read the main forest, leading-entry, remainder, stochastic-retract, realization, stability, finite-specialization and spectral proof chains and their worked examples. Corrected the nonzero workspace construction for purely real inputs and the false finite-support inference; defined the exact infinite valuation-error bound. Expanded transient-block decay, effective inversion, the real-part argument and crossover invertibility. Clarified valuations of nonzero eigenvalues, the rational-linear obstruction and the current algebraic Lean scope. A targeted follow-up supplied the discrete and one-block endpoints, strict coarsening and positive weights in the reversible converse, with explicit projection matrices and the one-state case. Checked the determinant and adjugate imports against Chebotarev–Agaev v2 with the same row orientation; other literature comparisons, priority and original-source reconciliation remain outside this review. |
| [Tail spans and differential transcendence](surreal/tail-spans-and-differential-transcendence/) | Read the coefficient-field, cofinite-span, polarization, exceptional-field, affine-plane, actual-surreal, mixed-jet, halo, approximation and undecidability proofs. Made characteristic hypotheses explicit and supplied a characteristic-two counterexample; replaced the abbreviated mixed-difference argument by finite Taylor operators, including degenerate directions. Expanded separating-functional construction, coordinate recovery and Galois splitting. Corrected the purported value-group enlargement from lexicographic integers to rationals, with the embedding specified. Aligned the partial Lean scope and rerun instructions, checked the extension-of-embeddings citation and local BM restriction, and distinguished cofinite tails from valuation prefixes. Other foundational imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Read the main support, reconstruction, sharpness, Hermite-precision and graph proofs and examples. Removed the graph theorem's divisibility assumption by auxiliary scaling and descent to the original Hahn field. Strengthened the classical uniqueness statement to arbitrary competing representations and the first-`2n−1`-moment rank obstruction, already covered in Lean. Corrected collision terminology, the measure-report comparison and stale formalization claims; checked the cited Caruso–Roe–Vaccon v1 hypotheses. A targeted follow-up restricted the equal-separation cluster formulas to at least two nodes and supplied the singleton threshold. |
| [Wick summability](surcomplex/wick-summability-certificates/) | Read the main support, semigroup, strict-alternative, diagram, connected-graph, covariance, identity and cancellation proofs and examples. Corrected the zero-semigroup boundary and proved the exact finite-sector criterion; added an integer-group counterexample explaining original-group divisibility. Extended the grouping proposition to a common nonzero complex factor and repaired the quartic comparison for signed Hahn tails. Specified monomial-insertion, zero-derivative and unit-exponent conventions and current partial Lean coverage. Checked the BM normal-form references and Etingof's normalized connected identity; other imports, literature comparisons and original-source reconciliation remain outside this review. |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Read the main support, escape, orbit, recurrence, differential, generic-line, dilation, theta, torsion and mixed-operator proofs and examples. Added inward stability of strong evaluation and used it to remove divisibility from the torsion equivalence. Repaired empty refined maxima, periodic starting indices and the unit-residue period choice. Replaced the false coefficientwise coarsening picture by a valuation on the same field, with a collapsing-support example; extended the explicit witness's short cofinal proof to arbitrary tails. Checked Stanley's recurrence correspondence and the local coarsening statement. The source-10 nonlinear review now covers Theorem D, Sections 14–17 and the corresponding Section 19.3 limitations. Expanded support regrouping, the finite initial layer, scale comparisons, denominator clearing and positive-weight finiteness; handled the constant-equation case and sharpened coefficient-degree wording. Added cancellation and same-solution-set/different-corner examples. Corrected the comparison of Euler and mixed-derivative criteria, a missing nonzero-equation summary hypothesis and an overbroad repository absence claim. Checked the targeted nonlinear predecessors, retaining Hu–Luan's characteristic-zero hypothesis. The source-11/12 review now covers Theorems E–G and Sections 20–22: expanded coefficient recovery, valuation rank and coarsened rational descent, corrected rank and boundary summaries, and supplied the mixed fraction-field corollary and a zero-rank independent example. Checked the imported classical SML scope and targeted predecessors. Other foundational imports, priority and original-source reconciliation remain separate. |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Corrected the three coordinate-family exact-domain clauses to exclude zero inputs. Subsequently read Sections 2–7: support calculus, formal inverse, normalization, exact theta and coordinate domains, coarse formal evaluation, rank-one completeness, formal germs, Taylor/Hahn agreement and the first uniformization/reduction proof. Removed the unnecessary characteristic-zero restriction from the formal inverse lemma while retaining later curve hypotheses; expanded finite normalization, convexity and maximality of the infinitesimal subgroup, and the completeness tail estimate. Added the fine-positive/coarse-zero counterexample to unrestricted evaluation and aligned the two coarsenings with the notation guide. Restricted the blanket no-divisibility claim to one-period uniformization, since classification and Part II have their own extra hypotheses. Checked the complete-field hypotheses and surjective kernel statement against Tate Theorem 1, and located the Jacobi product in DLMF 20.5.9. Subsequently read the second uniformization route and Section 9: universal specialization, integral node chart, smooth and infinity inverses, constructive surjectivity, the group law, support monoids and valuation geometry. Expanded actual-point uniqueness, assembled the normalized inverse in a chart table, clarified both support inclusions, and added discrete-value and rank-two examples. Checked the universal secant identities and generic-pair lemma against Tate pp. 6–7. Read Sections 10–13: scalar extension, value and residue sequences, extension obstruction, modular recovery, negative-j classification, torsion fields and surreal transfer. Corrected the conflation of the full value quotient with its real rank-one quotient and the description of the two coarsenings. Extended modular recovery to arbitrary characteristic-zero coefficients, added a nonsplit twist example, proved torsion exhaustiveness from the kernel theorem, and expanded the degree and class-obstruction arguments. Checked BPR Remark 4.24, Poonen Corollary 4 and the stated Molcho–Wise boundedness/Tate-curve precedent. Read Sections 14–17: finite-rank coordinate reduction, positive generation, one-level and flag summability criteria, and ordinal support length. Expanded primitive-lattice quotient arguments, explicit allocation, inheritance of the inductive hypotheses, non-full lattice reduction, and the translated-coset ordinal induction. Corrected the generating-set size bound to a cardinality bound and illustrated why finite exponent fibres are essential. Checked AN Definitions 2.5 and 11.10, Theorem 8.1, Question 11.14 and its rank-one construction in the published paper. Read Sections 18–21 and the computation/limitation notes: unit robustness, Taylor summation, quasi-periodicity, minimum certificates and graph geometry, initial polynomials, implicit substitution, smooth zero lifting and examples. Expanded finite-contribution bounds, directed enumeration and the infinite-parameter recursion; added sharp cube bounds and a singular zero with nonunique lifts. Corrected the coupled zero-row equation to use the coarse reduction of the full solution, with a nonzero higher-row witness, and corrected the preserved verifier's Python-version provenance. Checked the real-valued setting and tropical minimum formula in FRSS and the formal/convergent distinction in Joswig–Smith. Remaining imports and source reconciliation are pending. |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Read the shared support tools and Part I inner-product, automatic-adjoint, defect, normal-spectrum, inverse-smooth, coercivity, completeness, duality and norm-attainment proofs. Reconstructed the norm over arbitrary value groups, then removed the unused Part I divisibility restriction after tracing every root operation. Proved closedness of the coercive range at every rank using the continuous defect projection, retaining the original metric argument under its rank-one hypothesis. Added the positive-scale guard to the backward-shift example, distinguished valuation zero from metric distance one, and aligned the two inner-product conventions, summaries and hypothesis ledger. A subsequent Part II pass read the algebra, homogeneous diagonalization, normalization, synthesis, commutant, resolvent, walk, stability, finite-section, example and transport proofs. Corrected strict diagonal-coherence claims at finite index sets and trivial groups; supplied a coherent diagonal with incoherent inverse. Distinguished vectorwise Hahn projection additivity from classical strong-operator additivity, checked against Williams Definition 5.1, and gave a rank-one counterexample to pointwise valuation convergence. Expanded the sharp boundary coefficient’s formal root-comparison step and supplied its positive-length guard. A subsequent Part III pass reviews the Drazin, descent, halo, ramification, Banach and surreal proof chains; corrects the Volterra range and zero-inclusive power image; and extends the block vector obstruction to every nonzero infinitesimal. Part IV, remaining imported classical results, priority and source-claim reconciliation remain separate. |
| [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/) | Read the main support, scalar and matrix normalization, Harnack, null-ideal, functional, Fourier, quadrature, Schur, hierarchy and finite-prefix proof chains. Proved the Harnack, halo-positivity and common-kernel conclusions without divisibility by scalar normalization of quadratic forms. Expanded the zero-form and matrix-coefficient arguments; supplied the scalar-normalization positivity hypothesis and the integer-group obstruction to identity-block congruence. Corrected finite-valued versus finite-support terminology and the false disjointness of the strong and coefficientwise measure classes. Aligned partial Lean coverage and Fourier notation. Checked the classical disk representation against Bhattacharyya–Bhowmik–Kumar v3 and only the constant-kernel clause of Gesztesy–Tsekanovskii Lemma 5.3 against its preprint; other imports, priority and source-claim reconciliation remain outside this review. |
| [Expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/) | Read the main scale-ideal, inverse-branch, universal-center, fiber, periodicity, topology, extension, deformation, bounded-orbit and surreal-specialization proofs. Made degree preservation explicit in summaries and supplied a higher-degree two-cycle counterexample; clarified universal formal substitution and coefficient stabilization, and supplied the missing noncompactness argument. Distinguished an order unit from rank one, spelled out the proper-class specialization using set-sized compactness, and corrected the README’s ambiguous finite-orbit wording. Aligned partial Lean coverage and the notation guide. Checked the classical quadratic Cantor comparison and spherical Fatou/Julia definitions against Benedetto’s notes; other imports, priority and source-claim reconciliation remain separate. |
| [Finite surreal probability](surreal/finite-surreal-probability/) | Reviewed main text, Sections 2–17. Expanded workspace closure and standard-part existence, uniqueness, quotient and kernel arguments. Corrected the finite point-weight representation to require all subsets measurable; smaller finite algebras have atom weights. Expanded common-partition expectation, zero-second-moment Cauchy–Schwarz, tail bounds, finite Jensen, positive-denominator Bayes and chain rules, conditional tower and total variance, and both directions of finite coherence. Distinguished arbitrary versions on null atoms from pointwise identities and coherent laws from regular laws. Checked the canonical Hahn embedding and exponential transfer against van den Dries–Ehrlich Section 2 and its erratum. Expanded the conditional skeleton, its pairwise recovery, signed-row selection and Bayes leading coefficients. Corrected the joint-normalizer hypothesis for successive updates, neutral-likelihood wording, the difference numerator sign and sufficient-versus-necessary precision claim. Added the surreal-payoff and exact-threshold counterexamples. Checked the conditional-space comparison and real-payoff domain against Halpern Definition 2.1 and Section 4. Expanded logit inverse and domain checks, softmax gauge and perturbation bounds, separated-scale concentration, entropy and KL equality, support inheritance in the chain rule and data processing, and scoring identities. Distinguished the boundary logarithmic-score infimum from an attained interior minimum. Expanded Gibbs minimization, finite path consistency, adapted optional stopping and Bernoulli variance. Corrected the posterior-support claim after smoothing and the leading coefficient for a general infinitesimal scale. Added nonseparable logistic and non-stopping-time counterexamples and explicit zero-horizon cases. Expanded strong geometric regrouping, common-support coefficient measures, normalized hierarchy support and conditional shadows, real-observable dominated convergence and product Fubini, and the countable-support integration boundary. Distinguished uniform bounds from leading-component essential bounds. Expanded posterior coefficient measurability and added an explicit failure of coefficient integrability before density cancellation; checked the ordinary disintegration input against Kallenberg Theorem 8.5. Expanded the coin coefficient-variation bounds, polynomial-sign argument for relative field embeddings, ultrapower positivity, parity nonuniqueness and the finite compactness models. Replaced the logit change-of-variable shortcut with original Hahn leading data; distinguished finite-support permutations from unrestricted invariance. Checked the cited fine-ideal and fine-ultrafilter construction inputs. Expanded the rare-regime likelihood, martingale and full-observation conditional expectation calculations, supplied a fourth-moment proof of the component strong laws, and separated coefficientwise limits from the nowhere order-Cauchy conclusion. Expanded shadow continuity, internal-algebra measure extension and an explicit Poisson ultraproduct with diagonal saturation. Added a logarithm error bound, a measurable ordinary count and a Markov check for escaped mass. Aligned model weights, exponential hypotheses, notation and dependency claims in the final sections. Remaining imports and source/provenance reconciliation are pending. |
| [Three duals of Hahn vector spaces](surcomplex/three-duals-of-hahn-vector-spaces/) | Reviewed the main text, Sections 1–15. Expanded support facts, arbitrary regrouping, finite triple convolutions, the uniform shift bound and zero-group cases. Made the strong-map isomorphism and the descending-support counterexample explicit. Expanded coefficient-rank approximation by nets, nonzero-scalar closure and the countable-cofinal sequence construction. Corrected the guide's order-unit summary to distinguish strict completion from the noncyclic middle case. Expanded compatible-ball and Cauchy-net completeness, ball nesting, set-sized Zorn extension and its empty-chain case; corrected the claim that selecting one element of a known nonempty set separately requires choice. Expanded continuous restriction and separation, the canonical quotient kernel, cyclic finite-subsum convergence, Hilbert norm identities and topology, Riesz coefficients and cardinality. Corrected positive-versus-nonnegative bound scope at the zero operator and characterized bounds for unbounded leading coefficients. Expanded dense-kernel, projection, orthogonality and distance-cut proofs; distinguished an orthogonal complement from an orthogonal direct-sum complement. Expanded the cofinal/noncofinal induced topology, two-scale target topology, unique strong extension and normal-form transport. Corrected vector outputs described as scalars, the first-kappa comparison's missing properness hypothesis, spectral extension scope and stale negative-search/current-review claims. Checked BKKPS summability definitions, Kaplan–Krapp–Serra normal-form conventions and Morillon's real-valued one-step statement against primary text. Remaining imports/source reconciliation are pending. |
| [Hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/) | Reviewed the main text, Sections 1–11. Expanded character extension, finite support-index bounds, primorial degree, algebraic independence, closure minima, density and the workspace containing an algebraic surreal root. Expanded the positive-kernel lemma, arbitrary-ordered-field pivot argument, explicit Schur congruence and empty-block cases; detailed vector variation and scalar/vector null sets. Corrected the geometric-series witness for incomparable bases, restricted that comparison to rational exponents and explained containment when no order unit exists. Distinguished congruence from unitary diagonalization. Remaining imports, priority and original-source reconciliation are pending; no Lean mapping added. |
| [Bounded-support Hahn arithmetic](surreal/transcendence-over-bounded-support/) | Reviewed Sections 1–10 and the conditional implication in Appendix A. Expanded elementary support bounds, localization, coset and coefficient projections, tensor consequences, separated support bands, coding, top-rank grouping and normalized GCD descent. Replaced the factorial-family limiting argument by a finite Vandermonde proof. Corrected convergence to bounded initial truncations, with an explicit obstruction to finite-subsum convergence at uncountable cofinality. Clarified ideal extension, coefficient-field hypotheses and the neighbouring base-field comparisons. Checked the cited Hahn and rank-one imports against L’Innocente–Mantova v5; the GCD premise remains conditional. Remaining foundational/source reconciliation and priority are separate; no Lean mapping added. |
| [Matrix scaling at surreal scales](surreal/matrix-scaling-at-surreal-scales/) | Reviewed Sections 1–14 and the dependency appendix. Expanded finite-generator composition, complementary projections, formal coefficient recursion and unit inversion, recentering, tree replacement, chain base cases, positive scaling and local descent. Corrected evaluated-optimality wording for the trivial group, made strict feasibility on every support edge explicit, and separated formal tangent spaces from evaluated infinitesimal domains. Added the Hahn-valued constraint-minor counterexample and corrected two published theorem citations. Checked the current Markov, spectral and Prony comparisons. Other foundational imports, original-source reconciliation and priority remain separate; no Lean mapping added. |


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

The third critical-potential pass reviewed Sections 39–40. It separates
an exact Hahn sum from coefficients prescribed only at earlier scales,
gives an explicit ordinal bound including the empty case, and defines the
additive error class precisely. The field proofs now spell out set size,
inner-support bounds and independence, real/complex Hahn identification,
strong derivative closure, and the coefficient test excluding additional
solutions. The logarithm proof includes the full positive-element
factorization. The third field is now explicitly shown not to be closed
under logarithms: it contains `ℓ_λ` but omits `ℓ_{λ+1}`. The first two
fields' logarithm closure and the solution dimensions remain unchanged.

The Hahn real-closedness input was checked in BM arXiv v3, Section 2.3,
with a divisible ordered group. The PDF rebuilt in three passes at 197
pages, against a clean 195-page baseline, with no warnings or box issues;
the changed pages were inspected. Member 13's copied verifier passed all
70 finite checks with Python 3.13.14 and SymPy 1.14.0, matching its delivered
output apart from Python version. Those checks do not verify the new
transfinite support or logarithm-closure arguments. All 51 historical
artifacts remain byte-identical. The full Lean build passed 3,893 jobs
and audited 6,070 declarations using only `propext`, `Classical.choice`
and `Quot.sound`. The independent index verifies all 2,114 statements
across 44 reports, and all 879 local Markdown destinations in 93 files
resolve. Sections 41–42, remaining imports and source reconciliation are
still pending.

The final sync merged `84e51b5`'s finite trigonometric sign, monotonicity
and inequality proofs. The combined Lean build passed 3,903 jobs and
audited 6,092 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The differential-equations source and PDF were unchanged
by the merge. The independent index still checks all 2,114 statements,
and all 882 local Markdown destinations in 93 files resolve. The incoming
analytic results retain their stated scope and do not supply Lean proofs
for the critical-potential field constructions.

The fourth critical-potential pass reviewed Sections 41–42, completing the
Part VII main-text pass. It expands exponent-coset independence for arbitrary
Hahn coefficients, verifies the Borel substitutions and their inverses as
rational-field automorphisms, and records the composition convention,
additive subgroup and explicit noncommutativity. Schwarzian reconstruction
now states the algebraic square-root choice, invertible constant change of
basis and nonzero-denominator argument. The subcritical quotient's sign and
the first-limit finite-span calculation are explicit. The dependency table
now includes the actual angular primitive and the Schwarzian hypotheses.
The formalization route starts with finite differential-field algebra,
then Hahn support, then the intrinsic surreal interface.

The source comparisons check Krüger–Teschl's Section 2, equation (2.5) and
Corollary 2.3 with the potential sign reversed; the first-limit primitive in
Berarducci–Mantova's Theorem 8.4; and ADH's predicate with this report's
normalization `Ω(4Q)`. Versioned preprint links now match the cited versions.
This does not complete the other import or source-claim reconciliation.

Validation: the PDF rebuilt in three passes at 198 pages, versus 197 in the
baseline, with no warnings or overfull/underfull boxes in either final log;
changed proof and dependency-table pages were visually inspected. The copied
member-13 verifier reproduces all 70 delivered checks after removing only
the Python-version line. Separate exact symbolic checks cover the Borel
composition, inverse and conjugation, Möbius derivative and Schwarzian
invariance, and finite geometric/prefix identities of lengths 1–8. These
finite checks do not prove the transfinite or Picard–Vessiot assertions.
All 51 historical code/data/source artifacts remain byte-for-byte unchanged.
The independent index audit finds all 2,114 entries in 44 reports, and all
882 local Markdown destinations in 93 files resolve. Before the incoming
trigonometric-expansion merge, the full build passed 3,903 jobs and the axiom
audit checked 6,092 declarations using only `propext`, `Classical.choice`
and `Quot.sound`. The intrinsic Part VII results remain pending in Lean.

The final integration merged `465a54b`, including the exact infinitesimal
trigonometric expansions and normalization proof, through `ce1dcca`.
The incoming source mappings distinguish finite normalized remainders,
valuation identities and infinitesimal relative errors from sequence limits;
the fine-derivative and intrinsic-derivation boundary remains unchanged.
The combined build passed 3,906 jobs, and the axiom audit checked 6,127
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,114 indexed statements in 44 reports remain correctly catalogued,
and all 887 local Markdown destinations in 93 files resolve. The merge
left the reviewed differential-equations source and 198-page PDF unchanged.
This integration does not establish Lean coverage for its intrinsic
Picard–Vessiot or Schwarzian results.

The finite-probability review begins with Sections 2–3. The full event
algebra is now an explicit hypothesis for point-weight models; the trivial
two-point algebra demonstrates why point weights are otherwise not unique.
The expanded scalar and finite proofs cover standard-part uniqueness and
units, positive leading coefficients, common-partition expectation,
Cauchy–Schwarz at zero second moment, tail bounds and Jensen, positive
conditioning denominators, nested conditional expectations, total variance,
and the ticket identities characterizing coherence. Regularity remains a
separate condition, and null-atom versions do not affect scalar identities.
The canonical Hahn embedding was checked against van den Dries–Ehrlich
Section 2, p. 176, and the scalar exponential transfer against Corollary 2.2,
p. 177; the erratum changes ordinal support estimates, not that result.

Validation: three-pass baseline and revised PDFs are clean, with 41 and 43
pages respectively; the changed scalar, probability, inequality and
conditioning pages were visually inspected. All 114 source labels and their
numbers are preserved. The copied delivered verifier passes 2,145 assertions
and matches its recorded JSON apart from the Python version. A separate
953-check exact `Q(t)` run covers all 15 partitions of four points and
nested refinements, including zero masses, infinite payoffs, infinitesimal
thresholds, limited-unit residues and the additivity sure-loss witness.
These are finite examples, not proofs of the general or infinite statements.
All five historical audit/code/data artifacts are unchanged. The independent
index audit checks 2,114 entries in 44 reports; 890 local Markdown destinations
in 93 files resolve. The full Lean build passes 3,906 jobs and its axiom audit
checks 6,127 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. This source review adds no Lean coverage. Sections 4 onward,
remaining imports and broader source reconciliation still require review.

The final probability-core integration merged `e79b92a` through `2cda5fe`,
including the finite-angle quotient and canonical polar-group splitting.
Its source mapping retains the finite-angle domain and ordinary `2πℤ`
periods while allowing a nonzero surcomplex modulus of arbitrary size.
The combined build passes 3,912 jobs, and 6,214 declarations pass the axiom
audit with only `propext`, `Classical.choice` and `Quot.sound`.
The merge also brought in two packages placed in `d4e71b7`; their 67 base-source
statements are indexed provisionally, with assembly and review explicitly
pending. The independent index now checks 2,181 entries across 46 current
main sources (44 assembled reports plus two base manuscripts). All 903 local
Markdown destinations in 97 files resolve. The probability source and its
43-page PDF are unchanged by the merge, and the 30 newly delivered files
remain unchanged. This is integration validation, not a proof review of
the new foundations packages or additional probability Lean coverage.

The second finite-probability pass reviews Sections 4–5. It expands the
conditional-shadow product law and leading-scale formula, including empty
numerators, and shows how pairwise conditional shadows recover the ordered
leading groups and their coefficient ratios. The signed-row proof now makes
the well-ordered selection, dimension bound and coefficient argument explicit;
a two-state example shows why surreal payoffs outside ordinary `ℝ` are not
covered. The comparison with conditional probability spaces and real-payoff
equivalence was checked against Halpern Definition 2.1 and Section 4.

Three scope corrections matter for use: successive updates with zero
likelihoods require a positive joint normalizer; a neutral likelihood ratio
leaves the exact prior unchanged; and the strict valuation-error contract is
sufficient, not necessary for an individual pair of laws. The precision
clause now has its own positive-event hypothesis, and the exact difference
numerator has the correct sign. A rescaling example gives identical
conditionals despite larger input errors; a boundary example proves that
replacing the strict valuation bound by a non-strict one loses the stated
output precision. Infinite-logit persistence now includes the finite-sum
bound and the exponential argument for its unchanged real shadow.

Validation: clean three-pass PDFs at 43 pages in the baseline and 44 after
revision; the changed proof pages were visually inspected. All 114 label
numbers and all five historical audit/code/data artifacts are preserved.
The copied source verifier reproduces its 2,145 assertions, with the JSON
matching apart from the Python version. An additional 1,361 exact `Q(t)`
checks cover conditional products, scale recovery, compatible and impossible
joint updates, strict precision, cancellation, the payoff counterexample and
neutral odds. These are finite examples, not a general proof or an
implementation of surreal logarithms. The independent index audit checks
2,181 entries across 46 main sources (including two provisional bases), and
all 903 local Markdown destinations in 97 files resolve. The full build
passes 3,912 jobs and its axiom audit checks 6,214 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. Sections 6 onward and the
remaining imports still require review; probability Lean coverage is unchanged.

The final Sections 4–5 integration merged `ab36649` through `6f55757`,
including unique interval representatives, natural roots and the complete
polar root formulas. The source mapping was checked against the actual
interval endpoints, positive-degree hypothesis, nonzero input and positive
radius restrictions; the polygon result here is its side-length clause.
The combined build passes 3,916 jobs and 6,277 declarations pass the axiom
audit using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,181 indexed statements across 46 main sources remain correctly
catalogued, and all 907 local Markdown destinations in 97 files resolve.
The merge leaves the reviewed probability source and 44-page PDF unchanged.
This integration adds no probability formalization or review of later sections.

The third finite-probability pass reviews Sections 6–7. Logit Bayes now
states the interior-prior hypothesis and both positive likelihoods explicitly.
The finite state and scale lists are nonempty. The proofs expand logistic
inverses and the infinitesimal Taylor coefficient, softmax's exact common-shift
ambiguity, multiplicative perturbation bounds and the normalizer's logarithmic
bound, and the dominance argument for separated scales. The softmax “limit”
is explicitly a standard-part formula at fixed surreal inputs.

The information proofs now expose the nonnegative Gibbs slack terms, handle
positive-residue and zero-residue entropy coordinates separately, and justify
support inheritance in the chain rule and data processing. The data-processing
gap is an exact sum of conditional divergences, including infinitesimal
positive weights. The rare-entropy series and infinite-divergence example are
expanded. For logarithmic loss over strictly positive predictions, an interior
true law has its unique minimizer, while a boundary law has no minimizer.
Explicit redistribution strictly improves any interior prediction for a
boundary truth, and exponential smoothing attains arbitrarily small excess
above entropy, proving the infimum inside the workspace. Brier's full-simplex
identity and the logistic-loss identity are also expanded.

Validation: baseline and revised PDFs rebuilt in three passes without warnings
at 44 and 46 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
source verifier reproduces 2,145 assertions with JSON unchanged apart from the
Python version. Separate checks pass 813 exact `Q(t)` cases for softmax ratios,
gauge invariance, infinitesimal errors, boundary redistribution, smoothing and
Brier excess, plus 112 symbolic identities for logistic expansions, Gibbs slack,
entropy chain rules and data-processing gaps with zero coordinates/columns.
These finite checks do not implement arbitrary surreal exp/log or prove the
multiscale theorem. The independent index audit checks 2,181 entries in 46
current sources and all 907 local Markdown destinations in 97 files resolve.
The full Lean build passes 3,916 jobs; its axiom audit checks 6,277 declarations
using only `propext`, `Classical.choice` and `Quot.sound`. No new probability
Lean coverage is claimed. Sections 8 onward and remaining imports are pending.

The fourth finite-probability pass reviews Sections 8–9. Gibbs minimization
now includes its full-simplex domain, uniqueness at infinitesimal temperature,
and the ground-state shadow with a contrasting temperature-scale energy gap.
The finite decision argument includes the nonempty-act hypothesis and the
limited-payoff condition for standard part. Smoothing now distinguishes prior
regularity from posterior support and requires a positive joint normalizer
for successive updates. Its Hahn leading coefficient includes `lc(t)` for a
general infinitesimal scale, and the no-observation case is explicit.

The logistic-separation proof improves every candidate by a finite parameter
shift; an opposite-label example shows that a minimizer can exist without
separation. Finite path consistency is proved by terminal-coordinate sums,
including horizon zero. Optional stopping states adaptation, null-atom
versions and stopping-time measurability, expands the tower/pull-out proof,
and includes an anticipative-time counterexample. Rare hitting includes the
zero horizon, and Bernoulli variance and the failure of infinitesimal accuracy
at any ordinary sample size have explicit calculations.

Validation: baseline and revised PDFs rebuilt in three passes without warnings
at 46 and 47 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged apart from the Python
version. Separate checks pass 275 exact `Q(t)` cases for path marginals,
finite stopping rules (including null atoms and infinite payoffs), hitting,
Bernoulli moments and smoothing, plus 19 symbolic identities for Gibbs laws
and the opposite-label minimum. These finite checks do not construct an
infinite path law or compute canonical surreal exp/log. The independent index
audit checks 2,181 entries in 46 current sources, and all 907 local Markdown
destinations in 97 files resolve. No new probability Lean coverage is claimed.
Sections 10 onward and remaining imports are pending.

The following integration merges the actual surreal projective half-angle
formalization from `7ce5edd`/`f38a1ef` through `2a2d1c9`. The affine and
projective Cayley charts, direction multiplication, finite half-angle formula
and infinite-parameter proximity to the half-turn now have actual-surreal
Lean mappings. The full merged build passes 3,918 jobs and audits 6,313
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
The independent index still checks 2,181 entries in 46 current sources;
all 910 local Markdown destinations in 97 files resolve. The probability
source and 47-page PDF are unchanged by the merge, which adds no probability
formalization or review of its later sections.

A second synchronization through `9189e9d` incorporates `061d8f2` and
batch 21's assembly/catalogue/index commits. The actual inverse sine and
cosine cover their closed surreal input intervals, inverse tangent covers
all surreal slopes, and tangent's fine derivative is proved; inverse-function
fine derivatives remain pending. The merged build passes 3,919 jobs and
its axiom audit checks 6,371 declarations with only the three allowed axioms.

The two new foundations reports are now assembled and catalogued, with
61-page and 50-page PDFs and 136 indexed standard results. Their 26 delivered
audit/code/data files remain byte-identical to placement. The independent
index checks 2,250 entries across all 46 assembled reports, and all 930 local
Markdown destinations in 97 files resolve. These integration checks do not
constitute proof review of the new reports. The finite-probability source and
47-page PDF remain unchanged; review of Sections 10 onward is still pending.

The fifth finite-probability pass reviews Sections 10–11. Fine convergence
retains its relative-smallness hypothesis and is distinguished from a discrete
full carrier. The strong geometric law now has explicit event coefficients,
local finiteness under disjoint regrouping and exact tail masses. The
coefficientwise definition states finite total variation and one support for
all events, matching the measure report. The normalized hierarchy proof
expands the reciprocal, the common product support, the finite coefficient
measure formula and its total-variation bound, including the single-component
case. Conditional shadows explicitly handle a zero numerator residue.

Real-observable expectation uses a uniform real bound; the leading component's
essential bound alone fails on exceptional events, as an endpoint indicator
shows. Dominated convergence permits component-dependent null sets and is
coefficientwise only. The Fubini construction now covers any two set-sized
hierarchies in one value group, since their supports automatically satisfy
the Hahn product lemma. The uncountable-support positivity counterexample
has its scalar group and measure construction explicit; the countable-support
boundary has a transfinite first-nonzero-coefficient proof and the correct
finite-measure upper bound.

For finite-hierarchy posterior kernels, the density versions and their common
full-measure set are explicit. A finite union of positive-gap monoids supplies
a common support for all observations, and the coefficient formulas prove
measurability. The example with densities `2y`, `2(1−y)` on `(0,1)` gives
posterior `t(1−y)/(y+t(1−y))`: its first coefficient `(1−y)/y` is nonintegrable,
whereas multiplying by the observation density reconstructs `t/(1+t)`.
The ordinary disintegration input was checked against Kallenberg, third
edition, Theorem 8.5 in [Conditioning and Disintegration](https://doi.org/10.1007/978-3-030-61871-1_9),
with the observation as conditioning variable and the state as Borel-valued
variable. This verifies the imported scope, not a new surreal disintegration
theorem or a priority claim.

Validation: three-pass baseline and revised builds have no warnings, at 47 and
49 pages; changed proof pages were visually inspected. All 114 label numbers
and the five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged apart from Python
version. Separate checks pass 29,716 exact `Q(t)` examples for geometric
coefficients/regrouping, hierarchy shadows, product exponent collisions and
posterior cancellation, plus 12 symbolic coefficient and integral identities.
These finite checks do not establish transfinite support lemmas, countable
measure extension or the uncountable integration theorem. The independent
index checks all 2,250 entries across 46 reports, and all 930 local Markdown
destinations in 97 files resolve. The Lean build passes 3,919 jobs and audits
6,371 declarations using only `propext`, `Classical.choice` and `Quot.sound`.
No new probability Lean coverage is claimed. Sections 12 onward and remaining
imports are pending.

The following synchronization merges `872f921`/`1c4f513` through `bd4cf96`.
It completes the three actual inverse-trigonometric fine derivatives using
native interval continuity and a topological-field local inverse rule.
The ledger keeps subsequent series, infinite-slope asymptotic and endpoint
assertions separate. The merged Lean build passes 3,920 jobs, with 6,397
declarations audited using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,250 source-index entries remain correct and all 932 local Markdown
destinations in 97 files resolve. The probability source and 49-page PDF
are unchanged by the merge; it adds no probability formalization or review
of Sections 12 onward.

The sixth finite-probability pass reviews Sections 12–13. The two coin
obstructions now expose the common mechanism: real coefficient measures
would need unbounded total variation. The rare-coin first-success partition,
including its complementary all-zero event, gives `2N`; the fair-coin proof
expands pattern multiplicities, second/fourth moments, Hölder exponents and
an explicit finite contradiction threshold. Both exclude signed extensions.
The infinite negative-logit argument now uses the leading coefficient and
exponent of `exp(−L)` in the original Hahn coordinates; it does not assume
that this infinitesimal is a monomial or that changing coordinates preserves
coefficientwise measure structure.

The relative ordered-field embedding proof now constructs both real closures,
checks their size, uses the simplest element of each cut, proves polynomial
and rational-function sign preservation, and treats limit stages and the final
restriction to the original extension. The ultrafilter argument spells out
properness, fineness, nonprincipality, ultrapower order, positive singleton
masses and the infinite snapshot size. The even/odd example and the limits of
permutation invariance are expanded; the shift on the positive integers is
explicitly an injection, and a separate permutation witnesses failure of
unrestricted invariance under regularity. The shared notation guide separates
fine ultrafilters from the fine topology and scalar snapshot sizes from ordinary
cardinalities.

The extension theorem explicitly assumes an ordered subfield and a set-sized
language with a diagram that preserves the original constants. Its finite
models split each positive parent mass equally among nonempty refined children,
preserving all named old events and disjoint-additivity constraints. Different
finite models need not be compatible. Finite sample spaces admit the splitting
inside the original field; the coin corollary applies compactness over `R(t)`
and fixes the original `t`. Checked the construction comparison against
[Benci–Horsten–Wenmackers, arXiv Section 4.2](https://arxiv.org/pdf/1106.1524)
and [Brickhill–Horsten, Definition 4 and Propositions 5–6](https://arxiv.org/pdf/1608.02850).
These references support the sampling construction and its regularity/uniformity
scope, without identifying their infinite-sum convention with Hahn summation.

Validation: baseline and revised PDFs build in three warning-free passes at
49 and 50 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions, with JSON unchanged except Python version.
Another 5,650 exact finite checks cover coefficient variation and moments,
nonmonomial leading terms, finite atom-splitting models and parity snapshots.
They do not compute infinite ultrafilters, logical compactness, ordered-field
embeddings or countable measure extensions. The independent index checks
2,250 entries in 46 reports, and all 932 local Markdown destinations in 97
files resolve. The Lean build passes 3,920 jobs and audits 6,397 declarations
using only `propext`, `Classical.choice` and `Quot.sound`. No new probability
Lean coverage is claimed. Sections 14 onward and remaining imports are pending.

The following synchronization through `03b474b` merges ten Lean modules
from `debd084` and the placement `7b5f934`. The new modules cover Wick and
theta domains, Tate cubic lemmas, point-spectrum rigidity, polynomial-iterate
equicontinuity, invariant strong measures, finite visibility of negative atoms,
polynomial branch values and Prony cofactor bounds. Their source mappings retain
exact hypotheses and remaining clauses. All ten are imported by the default
root. The merged build passes 3,968 jobs and audits 7,045 declarations using
only `propext`, `Classical.choice` and `Quot.sound`.

Following the new source-reference check in `AGENTS.md`, all 2,542 distinct
referenced labels in the ledger and Lean docstrings resolve in current LaTeX
sources, including optional-argument labels. The placement adds two current
manuscripts with 48 standard results and source material for five existing
reports. All 49 newly placed files are preserved byte-for-byte. The two new
sources are provisionally indexed, giving 2,298 entries in 48 current sources;
the catalogue still covers 46 assembled reports. Their write phase and review
remain pending. All 964 local Markdown destinations in 108 files resolve.
The reviewed finite-probability source and 50-page PDF are unchanged by the
merge. No new Lean mapping is added for that report, whose Sections 14 onward
and remaining imports still await review.

The next synchronization, `6149ce2`, incorporates the inverse-tangent Taylor
formalization from `5e2b6e3`/`2638239`. The geometric inverse agrees with its
analytic lift at finite inputs, its odd-power strong series has the explicit
coefficients, and positive infinite slopes have an exact finite remainder
with the stated standard part. Inverse-sine coefficients and endpoint
ramification remain pending. No manuscript source changed in this merge.
The combined build passes 3,971 jobs and audits 7,074 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. All 2,542 referenced source
labels resolve; the independent index checks 2,298 entries in 48 sources,
and all 967 local Markdown destinations in 108 files resolve. The probability
review remains through Section 13, with its 50-page PDF unchanged.

The seventh finite-probability pass reviews Section 14. Positive integer
coordinate indices and the zero-observation case are explicit. Word
likelihoods derive the posterior, and the predictive success probability
`(1+M_n)/3` verifies its martingale identity directly. Component moments
give the exact nonzero covariance. A fourth-moment bound, Markov's inequality
and the summable real tail estimate prove both Bernoulli strong laws here.
The tail event's measurability, invariance under removal of an initial segment
and pullback to the joint space are explicit. The full-observation conditional
expectation is verified on every observation event using finite-range integrals.

The two exact consecutive-posterior differences have valuation one, so the
single order tolerance `t²` disproves the Cauchy condition on every path.
This includes paths where the real likelihood ratios tend to zero: on the
common-regime typical event, each Hahn coefficient tends to zero, whereas
on the rare tail event even the first coefficient tends to positive infinity.
The text distinguishes these real coefficient limits, standard-part limits,
order convergence and strong Hahn summation, without introducing surreal times.

Validation: the baseline and revised PDFs build in three warning-free passes
at 50 and 51 pages; the changed pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged except Python version.
Another 3,232 exact or symbolic checks cover word likelihoods, posterior
normalization and expectation, predictive updates, covariance, consecutive
differences, leading coefficients, geometric coefficients and centered fourth
moments. These checks do not compute infinite path events or prove convergence
theorems. The independent index checks 2,298 entries in 48 sources; all 967
local Markdown destinations in 108 files resolve. No Lean module changed in
this pass and no new probability formalization is claimed. Sections 15 onward
and remaining imports are pending.

A downstream consistency check also corrects two sentences in Section 16.
The conditioning precision contract is sufficient, not necessary for each
query with possible cancellation. An ordered field embedding fixing the
reals does preserve standard parts, directly from the inequalities defining
them; preserving exponentials, strong sums or internal structure requires
more. These targeted corrections do not constitute review of the rest of
Section 16. The PDF remains 51 pages after three warning-free passes, with
the affected page inspected and all 114 label numbers preserved.

Synchronization through `64e8a0e` incorporates `f8840cc`/`2cb9c02`.
The actual inverse-sine strong series now has explicit central-binomial
coefficients and a finite ninth-order remainder; inverse sine and inverse
tangent preserve exact valuation at infinitesimal inputs. The endpoint
ramification and derivative obstruction remain separate pending claims.
No manuscript source changed in this merge, and both added Lean modules
are included by the root import. The combined build passes 3,973 jobs and
audits 7,098 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. All 2,543 referenced source labels resolve. The independent
index still checks 2,298 entries in 48 sources, and all 969 local Markdown
destinations in 108 files resolve. These integration checks add no Lean
coverage for finite probability.

A further synchronization through `d93d5fd` incorporates `3e30b1f`, completing
the actual inverse-cosine endpoint half-angle identity, strong series, finite
remainder and half-valuation formula. The endpoint derivative obstruction
remains pending. No manuscript source changed. All three added modules are
root imports, and the merged default build passes 3,976 jobs with 7,116
declarations audited using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,545 cited source labels, 2,298 indexed entries in 48 sources and 972
local Markdown destinations in 108 files pass their checks. The reviewed
probability source and 51-page PDF are unchanged by this integration.

The eighth finite-probability pass reviews Sections 15–17 and aligns the
introductory and appendix dependency notes. The shadow-continuity theorem
now proves real finite additivity first, expands both directions of continuity
from above, and distinguishes real tolerances from arbitrary surreal ones.
The Loeb construction specifies its internal event algebra and probability,
uses saturation on internal remainders to prove the premeasure property,
and distinguishes the unique real measure extension from its completion.
An ordered embedding fixing the reals preserves that real measure but does
not provide its internal events or preserve internal exponentiation.

The Poisson model is now a defined ultraproduct of finite product experiments.
Its internal probability is well-defined, and a diagonal selection proves the
countable saturation needed for Loeb extension. A quantitative real logarithm
bound gives the fixed-count limit, including the empty-product case. The
ordinary finite-count event is Loeb measurable and has measure one; the
resulting ordinary nonnegative integer-valued variable has the exact Poisson
law. A separate Markov estimate shows that no mass escapes to infinite counts.
The written infinite arguments are distinct from computations at finite sample
sizes. Loeb's publisher text remains unavailable in this pass; the historical
metadata-only citation boundary is retained, while the finite-probability
construction is spelled out from saturation and ordinary measure extension.

The implementation interface now permits nonnegative weights with positive
total, retaining exact zeros; strictly positive weights describe regular laws.
It places Brier scoring in the ordered-field layer and names the exponential
isomorphism and scalar inequalities needed for the logarithmic results.
Dependency notes now record the Bernoulli strong laws as proved here, while
product-law existence and real disintegration remain imported. The scope
section corrects an overstatement about full fine countable additivity:
finite-support laws do satisfy it by eventual stabilization. What is absent
is a general infinite sampling theory under that rule. The notation guide
separates the internal and Loeb probabilities and the internal and ordinary
counts, and distinguishes the two local meanings of `H`.

Validation: baseline and revised PDFs build in three warning-free passes at
51 and 53 pages, with changed pages visually inspected. All 114 label numbers
and the five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged except Python version.
Another 7,269 exact rational checks cover binomial normalization, means,
factorization, Markov tails and independent enumeration of word probabilities.
They do not implement an infinite ultrafilter, saturation or Loeb extension.
The independent index checks 2,298 entries in 48 sources, all 2,545 cited
source labels resolve, and all 972 local Markdown destinations in 108 files
resolve. This completes the Sections 2–17 main-text review; remaining imports
and source/provenance reconciliation still require work. No new probability
Lean formalization is claimed.

Synchronization through `b6c2493` incorporates `6437ec3`/`f16a616`.
The inverse-sine endpoint module proves inward difference quotients exceed
every fixed actual surreal bound, including infinite bounds, and excludes
both one-sided endpoint derivatives and ambient fine derivatives. Its root
import and the corresponding source scope were checked. No manuscript source
changed in this merge. The combined default build passes 3,977 jobs and audits
7,127 declarations using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,545 cited source labels resolve; the independent index still checks
2,298 entries in 48 sources, and all 973 local Markdown destinations in 108
files resolve. The reviewed probability source and 53-page PDF are preserved;
this integration adds no Lean mapping for that report.

The first three-duals pass reviews Sections 2–5. The support proof makes
choice, the nondecreasing-subsequence argument and finite coefficient fibers
explicit. Regrouping includes empty fibers, and triple-support finiteness
justifies scalar associativity and the canonical strong-map isomorphism.
The valuation-shift proof names its target neighborhood, handles zero values
and treats the zero group separately. The operator calculus identifies its
identity and central scalar action; cancellation yields an inequality rather
than an equality of valuations. The pointwise-support example now uses
`Γ = Q`, exponents `1/n` and an explicit Hahn vector whose putative image
has infinitely many contributions at zero, in every coefficient characteristic.

The completion criterion specifies the induced uniformity and its net of
truncations, and handles zero scalars before subtracting their valuations.
The countable-cofinal construction builds an increasing cofinal sequence
without assuming an order unit; the converse chooses independent coefficients
below a common cut. The guide's order-unit summary is corrected: it gives
`E ⊊ C`, but yields the middle case only for noncyclic groups. All infinite
formal sums in these proofs use the shared strong-sum notation.

The completeness proof expands compatible ball prescriptions and uniform
stabilization of Cauchy-net truncations, including the zero group and empty
ball family. The Hahn–Banach proof writes out ball containment, uniqueness
and linearity of the one-vector extension, and the set of partial extensions
used by Zorn, including the empty-chain upper bound. It corrects the claim
that selecting one element of a known nonempty intersection separately uses
the axiom of choice. Independent reviews checked the completion boundaries,
the edited support/operator proofs and the extension argument; the final
empty-chain clarification arose from that review.

Validation: three-pass baseline and revised PDFs are warning-free at 34 and
35 pages, and changed pages were visually inspected. All 77 source-label
numbers (154 including cleveref companions) and three historical audit/code/data
files are preserved. The delivered verifier reproduces all 610 assertions
with byte-equivalent JSON data. A separate 2,800 exact sparse-convolution
checks in characteristics 2, 3, 5 and 7 cover scalar compatibility, operator
composition, additivity, identity, direct triple expansion, finite regrouping
and valuation shifts. These finite checks do not establish infinite support,
completion or choice-based extension. The independent index checks 2,298
entries in 48 sources, all 2,545 cited labels resolve, and all 976 local
Markdown destinations in 108 files resolve. Sections 6 onward and remaining
imports/source reconciliation are pending; no new Lean mapping is claimed.

A separate independent reading of the revised finite-probability Sections
14–17 found no error in the latent martingale, shadow-continuity criterion,
Loeb premeasure construction, diagonal saturation, Poisson logarithm bound
or measurable ordinary count. This checks the stated proof scope, not the
unavailable full Loeb source or the report's remaining provenance obligations.

### Batch-22 assembly and phase-isometry integration

Merged the batch-22 assembly and catalogue through `37eefca`, followed by
the local phase-isometry and arbitrary-radius rotation results in `cd80e5e`.
The independent inventory now checks 2,440 standard statements in 48
assembled sources. All 45 delivered batch-22 audit, code/build and data
artifacts are byte-identical to their placement versions. The five expanded
reports retain their old labels; the two new reports retain all delivered
labels with their assembly prefixes. The catalogue has 48 entries.

An independent comparison of the changed manuscripts checked all 120 labels
cited by the current Implementation mappings: 35 in holonomic rigidity,
47 in trigonometry and 38 in Hahn measures. Their statement environments,
and the mapped subsection `hol:sub:coarseboundary`, are unchanged. The
surrounding conventions do not change their hypotheses. This preserves
existing mappings; it does not review the newly added mathematical claims.

Corrected first-kappa's provenance in its source and guide: raw placement
was `7b5f934`, while the editorial additions and report assembly were
`68e2960`. Baseline and revised PDFs both have 25 pages, with three clean
passes and visual checks of the changed pages. All 77 label numbers,
23 standard statements, 22 proofs and five historical artifacts are
unchanged. This is a provenance correction, not a proof review.

The merged Lean build passed all 3,984 jobs; the default axiom audit passed
for 7,210 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. All 2,695 cited source labels and 1,015 local Markdown
destinations in 108 files resolve. Six incoming gamma/zeta archives remain
unassembled and are outside the main-source inventory.

### Three-duals continuous duality and Hilbert geometry

The next three-duals pass reviews Sections 6–9. It verifies closure of the
restriction space under scalar operations, explains why independent constants
prevent leading cancellation, and expands the separation of every vector
outside the coefficient-rank completion. The second quotient now has its
canonical map and exact kernel written out. The finite-dimensional proof
correctly uses a coefficient-space basis, and the cyclic argument gives the
finite-index sets, shifted cuts and finite-subsum nets that justify continuity
implying strongness. The constant-one obstruction is explicitly independent
of characteristic; the zero-group endpoint is recorded separately.

The Hilbert pass expands norm homogeneity, the real-part comparison in the
triangle inequality, explicit norm/valuation neighborhoods, strongness of
represented functionals, the adjoint convention and the cardinal quotient
argument without a continuum hypothesis. It corrects a citation-scope error:
the spectral norm-attainment theorem uses nonnegative bounds on nonzero
coefficient spaces. The zero operator has least nonnegative bound zero but
no least positive bound. For an ordinarily unbounded leading operator
coefficient at exponent `s`, all positive Hahn bounds are characterized by
`v(M) < s`; they need not be the monomials displayed as examples.

The hyperplane pass gives the ordinary dense-kernel contradiction, the
algebraic direct sum and projection bound, and the exact identity
`v(u-m) = min(0,v(m))` for distances from an exterior constant. It distinguishes
the existing zero orthogonal complement from the absent orthogonal direct-sum
complement. The distance statement repeats the existing nonzero-group
convention, and the proof excludes every possible infimum, including zero.
Independent reviews of all four revised sections found no further issue.
The appendix now also reflects the earlier correction from a claim of two
uses of choice to the set-sized Zorn argument actually used.

Validation: baseline and revised PDFs compile in three warning-free passes,
at 35 and 37 pages; the changed pages and contents were visually checked.
All 77 source labels and numbers (154 with cleveref companions) and all three
historical audit/code/data artifacts are preserved. The delivered verifier
reproduces its 610 exact assertions and byte-identical JSON. These finite
checks do not establish infinite-dimensional duality or the choice-based
constructions. The independent inventory checks all 2,440 indexed statements
in 48 sources; all 2,695 cited source labels and 1,015 local Markdown
destinations resolve. Sections 10 onward and remaining imports/source
reconciliation are pending. No Lean coverage is added by this proof review.

Merged `fc1c12a` after this review, adding the actual-surcomplex direction
stability formalization and its root imports. No manuscript source changed
in that merge. The combined Lean build passed all 3,987 jobs; the default
axiom audit accepted 7,253 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. The statement index remains at 2,440
results in 48 sources, all 2,695 cited labels resolve, and all 1,018 local
Markdown destinations in 108 files resolve. The merge preserves the reviewed
three-duals source and PDF exactly.

### Three-duals enlargement, interpretation and source comparisons

The three-duals review now covers the main text, Sections 1–15. The final
pass expands coefficient preservation, both inclusions in the cofinality
theorem, and the induced-topology dichotomy: a cofinal inclusion preserves
the old intrinsic topology, while a noncofinal inclusion induces the discrete
topology. The zero coefficient space and zero-group endpoint are explicit.
The two-scale example gives its tail valuations and all-approximants rank
obstruction. Its functional is restricted into the larger scalar field with
that field's Hausdorff intrinsic topology; using only old thresholds there
would lose Hausdorffness. Strong operator extensions are unique among strong
extensions, and the represented-functional and hyperplane constructions are
checked coefficientwise.

Expanded the normal-form embedding's injectivity, arithmetic, order and strong
sums, and the isolation of old scalars by full-surreal tolerances. Corrected
general operator outputs described as scalars: they remain module vectors;
norms and scalar-valued functionals supply scalar values. The same fine
isolation argument for Hilbert modules is explicitly about norm balls.

The local comparisons now restrict spectral persistence to its constant-normal
and specified positive-order-defect cases. First-kappa's completeness summary
includes its standing hypotheses and properness condition; without properness,
`Γ = Q`, `κ = aleph_omega` already contradicts the omitted-hypothesis version.
The old absence search is pinned to placement, recognizing the later report's
explicit comparison. The guide's duplicated stale review status is replaced
by the current scope and a link to this history. Inventory entries are
distinguished from Implementation mappings; no new Lean coverage is claimed.

Primary-text checks covered [BKKPS §§1.1–1.3](https://arxiv.org/pdf/2403.05827v2),
including Definition 1.19, Example 1.7 and Definition 1.1's finite-copy
ultrafiniteness. Corrected the attribution of nonstrong examples, which that
paper refers to earlier work. Coefficient-field ultrafiniteness is explained;
term-dependent Hahn scalars can destroy summability. Checked the normal-form
sign convention in [Kaplan–Krapp–Serra §§2.2 and 2.4](https://arxiv.org/html/2509.22374v3)
and the classical mechanism in [Morillon §3.1.2, Lemma 2](https://arxiv.org/html/1901.04021).
The latter uses real-valued seminorms over spherically complete valued fields;
the report supplies its own arbitrary-ordered-group proof. These are targeted
checks, not a complete audit of imported results or a priority certification.

Validation: independent mathematical and source-scope reviews passed after
clarifying the locally chosen positive exponent and the meaning of losing
completion membership. Baseline and revised PDFs build in three warning-free
passes at 37 and 39 pages; changed pages, comparison tables and bibliography
were visually checked. All 77 label numbers, all 29 standard statement
environments, and all three historical audit/code/data files are unchanged.
The delivered 610 assertions reproduce byte-identical JSON. The independent
index checks 2,440 results in 48 sources; all 2,695 cited labels and 1,019 local
Markdown destinations resolve. Remaining imported-result and source
reconciliation work is separate from this completed main-text reading.

Merged the triangle-angle formalization and gamma/zeta placement through
`d2752d8`. The merge leaves the reviewed three-duals source and PDF unchanged
and changes no previously mapped manuscript statement. The Lean build passed
all 3,990 jobs; the default axiom audit accepted 7,287 declarations with only
`propext`, `Classical.choice` and `Quot.sound`.

An independent archive-member comparison verifies all 31 gamma/zeta files
placed in `e4f8848`: two raw main files from manuscript 06 and 29 historical
code/build/data artifacts from the six archives. The sole CRLF CSV retains
all 738 bytes and 24 CRLF pairs, with its `-text` attribute. The current
main source has 25 standard statements, 104 unprefixed labels and two
unlabeled corollaries. Five labels collide with other reports, so index
navigation includes the source path. The delivered guide still names old
package paths and its 28-page source PDF; no assembled report PDF is present.
Those write-phase tasks remain pending, and the other five source texts
remain recoverable from the archives in Git history.

The provisional source index now covers 2,465 statements in 49 current main
sources, comprising 48 assembled reports and this placed base manuscript.
The independent audit verifies the counts, headings, labels and line anchors;
all 2,719 cited source labels and 1,025 local Markdown destinations in 109
files resolve. This adds navigation only, not mathematical or Lean coverage
of the new report.

The final sync also merged `7666865` through `ab48639`, completing the
incoming triangle-law and circumcircle work. The overlapping Gamma/zeta
inventory edits were reconciled into one source row and one provisional
statement section; the entire incoming Implementation mappings section is
preserved verbatim. No manuscript source or delivered artifact changed.
The combined build passed 3,994 jobs and audited 7,413 declarations using
the same three permitted axioms. The independent 49-source index remains
clean, and all 2,720 cited labels and 1,030 local Markdown destinations resolve.

## Hidden-negative-directions main-text review

The [hidden-negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/)
review covers Sections 1–11. Independent readings checked the support and
character arguments, prime-tail separation and independence, inertia, closure,
density and transport, and the two-scale matrix and measure criteria. The
core statements remain valid under their stated hypotheses. Character
extension now proves well-definedness on the enlarged subgroup, the finite
support quotient is identified explicitly, and the degree proof shows both
Bézout generation and the radical upper bound. Formal evaluation spells out
well-ordered finite sums and finite tagged contributors, including zero inputs.

The bounded-support comparison contained an invalid witness: the unbounded
geometric series `Σ_{n≥1} t^n = t/(1−t)` is itself a fraction of finite-support
series. For `Γ = ℚ`, the replacement `√(1+t)` belongs to the probe field but
not the bounded-support fraction field. The article gives the integer-coset
projection proof and rational-square obstruction, checked also against
`bst:cor:onescale`. Incomparability is not asserted for all groups: without
an order unit each finitely generated subgroup is bounded above, so the
probe field lies in the bounded-support ring. The guide and nonclaim ledger
now use the same scope. The spectral comparison also distinguishes the
explicit triangular congruence from unitary diagonalization.
The tail-spans comparison now specifies algebraicity over the whole
coefficient Hahn field via one finite coefficient extension, rather than
merely having algebraic individual coefficients. Its monomial-field
obstruction cites the probe-closedness and barrier results, and the
coefficientwise-additivity comparison is limited to the null-ideal results.

The closure proof now verifies preservation of the least coordinate
valuation. The density proof gives an explicit ordered-field continuity
estimate. For a surcomplex algebraic root, the proof first forms a nonzero
set-sized workspace containing its normal-form support and the equation's
parameters, then applies the character bound to shrink the support.
The two-scale matrix proof defines compression unconditionally, gives the
positive-pivot argument over an arbitrary ordered-field complexification,
and displays the Schur congruence and all empty active-block cases.
The measure proof bounds vector total variation by the entry variations and
makes the finite-partition and Jordan-decomposition null-set steps explicit.

The baseline and revised PDFs each compiled in three clean `pdflatex`
passes; the current report has 33 pages (previously 31). All 89 labels and
result numbers are preserved. Of the 24 standard result environments, 22
are byte-identical; the two changes clarify intrinsic valuation topology
and define `ker P` and its compression before testing positivity.
All seven delivered audit/code/data files remain byte-identical.
The delivered exact verifier passed under Python 3.13.14 and SymPy 1.14.0,
matching historical JSON except for the Python version: 35,100 prime-coset
comparisons, 5,946 real matrix pairs with 1,823 positive cases, plus the
congruence, orbit and example checks. A separate scratch diagnostic checked
390,625 Hermitian 2×2 pairs, including complex off-diagonal entries, against
principal-minor leading signs; all agreed and all 18,145 positive cases
also matched the rank formula. Those finite checks do not prove arbitrary
Hahn-support or measure assertions. Remaining imports, literature priority
and original-source reconciliation remain outside this main-text review.
The rendered comparison, proof and appendix pages were inspected; the final
comparison edits changed only physical pages 7–9, which were checked again.

The sync merged `cfdcdc0` through `6980af8`, adding the complete right-triangle
corollary. No incoming manuscript source changed. The combined
`LEAN_NUM_THREADS=2 lake build` passed 3,995 jobs; the axiom audit checked
7,429 declarations and used only `propext`, `Classical.choice` and `Quot.sound`.
The independent 49-source index remains clean at 2,465 statements, and all
2,720 cited source labels plus 1,035 local Markdown destinations resolve.
This validation preserves the distinction between the new Lean triangle
mapping and this report's mathematical proof review.

## Bounded-support main-text review

The [bounded-support report](surreal/transcendence-over-bounded-support/)
review covers Sections 1–10 and the conditional implication in Appendix A.
Independent readings checked the elementary support and localization facts,
cofinal descent, separated exponents and polynomial support bands, coefficient
coding, explicit families, rank structure and the surreal specializations.
The proofs now spell out coset projection without treating it as a ring map,
the finite-dimensional domain argument for algebraic degrees, and the
noncofinal tensor-kernel witness. The integer-grid statement specifies a field;
the descent preview now describes the ideal generated after scalar extension.

The support-band proof makes the surviving coefficient and its two strict
gaps explicit. The countable multiplicative-parameter family now uses a finite
Vandermonde matrix over the Hahn field: among a sufficiently late block of
consecutive evaluations, at least one is nonzero. No ordinary limit of Hahn
coefficients is needed. The countable code's starting index is aligned with
the delivered program, and the arbitrary-cardinal coding argument retains
its singular-cardinal scope.

The convergence prose previously conflated bounded initial Hahn truncations
with finite subsums. Initial truncations of the constructed cofinal support
have cofinal error valuations. For uncountable cofinality, every finite subset
misses a term before the first limit index, so its error cannot enter the
neighborhood beyond that limit exponent. The article, guide and notation
reference now distinguish these nets and explain why full surreal fine
convergence still fails.

The rank proof constructs the maximal proper convex subgroup explicitly,
checks the iterated Hahn presentation in both directions, and applies the
rank-one upper-support formula only after passage to an Archimedean quotient.
The imported closedness, iterated presentation, nonrationality obstruction
and upper-support theorem were compared with L’Innocente–Mantova's cited
v5, including the locations and hypotheses. Normalized GCD descent now
includes the character-extension well-definedness and normalization steps.
The GCD existence premise remains unproved here; no external Lean project
was built or adopted. Other foundational imports, original-source
reconciliation and literature priority remain separate obligations.

Local comparisons distinguish full coefficient Hahn fields from bounded
fraction fields, sufficient almost-disjoint families from unrestricted
index sets, and the rational-exponent incomparability of two fields from
containment when no order unit exists. Historical keyword counts are scoped
to their pinned snapshots. Source inventory is distinguished from an
Implementation mapping; this review adds no Lean proof coverage.


The baseline and revised PDFs each compiled in three clean LaTeX passes;
the revised report has 31 pages (previously 29). All 73 source labels and
result numbers are preserved. Of the 30 standard result environments, 28
are unchanged and two have only the ideal-extension and coefficient-field
wording clarifications above. All seven delivered audit/code/data files
remain byte-identical to both the previous source revision and raw placement;
the six applicable historical manifest digests match. The delivered verifier
passes all 3,163 assertions in 12 groups under Python 3.13.14, matching its
recorded JSON except for the Python version. Those finite checks do not
prove transfinite or cardinal assertions. All revised pages were visually
inspected, including the corrected Theorem 8.2 page break.

The 49-source inventory remains at 2,465 standard statements. Its independent
audit reports no count, heading, label or anchor issues; all 2,720 cited
source labels and 1,040 local Markdown destinations in 109 files resolve.


The sync merged triangle reconstruction and incircle work through `c74287c`.
No incoming manuscript source changed. The combined
`LEAN_NUM_THREADS=2 lake build` passed all 4,009 jobs; the default axiom audit
accepted 7,688 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The independent 49-source index remains unchanged, and all
2,723 cited source labels plus 1,054 local Markdown destinations resolve.
The incoming triangle mappings remain distinct from this documentation review.

## Batch 19 provenance correction

The four new reports in batch 19 cited an unavailable placement hash,
`52c7ab6`. Retained Git history identifies raw placement as
`30dfb4f5b794818315af63ab6f4215337e68dec8` and its child, editorial assembly
and the first compiled report PDFs, as
`ed88b8f6a3901d4cbcf8e4249673161f493f679b`. Their articles and guides now
attribute placement, editorial additions, PDF comparisons and historical
search counts to the appropriate snapshot. This does not infer why the
unavailable hash was recorded.

The three-duals, hidden-negative-directions and matrix-scaling provenance
changes preserve all mathematical statements and proofs. Their baseline and
revised PDFs each passed three clean LaTeX passes and retain 39, 33 and 32
pages respectively. All 260 source labels and their numbering are preserved;
all 19 historical audit/code/data files remain byte-identical. The 19 changed
PDF pages were visually inspected. Matrix scaling has received this
provenance correction only; its mathematical proof review remains pending.

## Matrix-scaling main-text review

The [matrix-scaling report](surreal/matrix-scaling-at-surreal-scales/)
review covers Sections 1–14 and the dependency appendix. Independent readings
checked the elementary support and tree identities before the normalization,
secant gain, coefficient bounds, combinatorial certificate, nonlinear chain,
global positivity, real-constraint extension and surreal transport. The core
statements remain valid under their intended hypotheses.

The finite-generator evaluation proof now bounds both inner and outer formal
degrees at each Hahn exponent, explicitly licensing composition. The tree proof
identifies all four projection images and kernels and distinguishes row from
column minors. The formal argument uses a weighted Laplacian whose constant
term is invertible; its formal inverse is used algebraically, while strong
evaluation still depends on the finite-generator lemma. Recentering displays
its cut and conservation equations before invoking uniqueness. The remainder
certificate specifies a nonnegative integer degree, including zero, and handles
bridge rows and the relative-output series explicitly.

The evaluated “largest uniform gain” claim needs a nontrivial value group:
for the trivial group the infinitesimal domain is a singleton. The article,
guide and notation reference now retain the formal coefficient assertion in
that case without claiming an evaluated witness. Formal tangent spaces are
identified at each balanced point and distinguished from the infinitesimal
domain. Strong summability is no longer described as excluding partial-sum
convergence; it does not imply convergence on its own.

The one-minimum-tree certificate now includes its exchange proof. The chain
proof states both continuant base cases and checks the `n = 2` case.
The positive-normalization comparison explicitly requires a feasible matrix
positive on every prescribed support edge, with a triangular-support
counterexample to mere positive margins and nonnegative feasibility. Its cut
bound now explains why root-normalized factor ratios are infinitesimally close
to one. The real-constraint proof handles zero columns, coloops and empty
systems; a Hahn-valued row `(1,t^β)` shows the missing minor valuation in a
formula using entry costs alone. The phase example gives its exact discriminant.

The published comparison now cites continuity as Idel Theorem 4.5 in v1,
and generalized Dirichlet expansions as Sharify–Gaubert–Grigori Theorem 2.4
in v2, with the nonnegative square matrix and total-support setting explicit.
These passages, Eisenberger et al.'s implicit projection and approximate-input
analysis, and Burton–Pemantle's transfer-current background were checked against
primary sources. This does not independently re-audit every foundational import
or certify priority. Current Markov, spectral and Prony source comparisons were
checked at `034ab96`; the Prony certificate retains its strict-ball hypotheses,
and the spectral geometric-series example is distinguished from this report's
exponential example. Historical searches and delivered self-audits remain dated
evidence, and the 16-statement inventory remains distinct from Lean coverage.


The baseline and revised PDFs each passed three clean LaTeX passes, with no
warnings or box notices. The revised report has 33 pages (previously 32),
with the bibliography kept together. All 94 source labels and 188 auxiliary
numbering entries are preserved. Of the 16 standard results, 13 are unchanged;
three clarify the remainder degree, strict support feasibility and the empty
basis-minimum convention. All nine historical audit/code/data files remain
byte-identical to the baseline and raw placement. The unchanged exact verifier
passes every group under Python 3.13.14 and SymPy 1.14.0, reproducing the recorded
JSON except for the Python version: 2,056 projection entries, 2,612 edge gaps,
four formal recurrence examples, 55 chain inverse entries and three square
identities. These finite checks do not prove the general Hahn assertions.

All revised pages were visually inspected. The independent source-index audit
still checks 2,465 statements in 49 main sources without issues; all 2,723 cited
labels and 1,059 local Markdown destinations resolve. The review table now keeps
both recent reports inside the same Markdown table. No Lean coverage is added
by these documentation checks.


The sync merged Euler's triangle-center identity, the radius inequality and
the sharp area bound through `14bb32b`. No manuscript source changed.
The combined `LEAN_NUM_THREADS=2 lake build` passed 4,014 jobs, and the
default axiom audit accepted 7,737 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. The independent 49-source index remains
clean; all 2,724 cited source labels and 1,064 local Markdown destinations
resolve. The incoming Lean mappings remain distinct from this mathematical
review of the matrix-scaling report.


A final sync merged `e439806`, adding cevian sine ratios and trigonometric
Ceva, again without changing a manuscript source. The rebuilt combination
passed 4,024 jobs and audited 7,827 declarations using the same three permitted
axioms. All 2,726 cited source labels and 1,070 local Markdown destinations
resolve; the 49-source statement inventory is unchanged.

## Nonscalar dynamics main-text review

The [dynamics report](surcomplex/dynamics-and-normal-forms/) review now covers
source 10, Sections 7.7–7.13 and the corresponding Section 26.10 limitations.
Independent readings checked the elementary angular-rate argument before the
colored-tree contraction and product estimate, then formal expansion, common
domains, inversion, the exact criterion and examples. The earlier dynamics
review and the other source packages retain their separately recorded scopes.

The determinant proof now handles an empty family, gives its integer-cofactor
bound and quantifies the contradiction between two distinct exponential rates.
The nearest-integer reduction records its height bound and preservation of
rates. Linear height is sufficient, not necessary: the proof works for
subexponential heights. The rate-count conclusion also extends to a fixed
infinite family by finite-subfamily restriction, without a uniform eventual
rank bound or a bound on sums over growing multiplicities. A Fibonacci example
exhibits two positive rates for one real variable at exponential heights.
These observations correct the necessity wording without changing the numbered
height lemma used by the tree proof.

The finite-prefix construction of the divisor constant and the fixed-skeleton
subsequence bounds are explicit. The rank-one product equality handles infinite
rate directly by its one-vertex lower bound. The formal expansion distinguishes
Hahn labels `η_v` from integer subtree weights `s_v`, restricts word depth to
supported nonzero exponents, and specifies the coordinate slots responsible
for multinomial multiplicities. Its least-difference uniqueness proof applies
to any normalized positive-support competitor. The common-domain proof covers
empty support and expands the multivariable root test into normal convergence.
The inverse proof records inclusion of the input ancestry sets, so finite
products and derivatives preserve the same open domain. Rectangular radii use
finite diagonal rescaling and exhaustion for infinite entries; ordinary
parameter dependence is explicitly joint holomorphy.

The exact criterion and the two-mode and algebraic examples check out. The
zero-rate case has universal radius exactly `R` at every angular rank. The
article, guide and hypothesis table now restrict the undetermined higher-rank
optimum to `0 < τ < ∞`. A subsequence proof supplying no effective formula is
no longer described as proving noncomputability. The nongrid example is
identified as one example, and strong summability does not presume convergence
of partial sums in the fine topology. The notation guide separates angular
rank, value-group rank, ordinary radius and tree complexity.

The targeted primary comparison checked Fauvet–Menous–Sauzin arXiv
2507.13216v2, Sections 5.1–5.3 and its Section 6.1 usage. Admissible-cut closure
is Theorem E, for forests whose associated operators are not universally zero;
Proposition 5.6 supplies the homogeneity-degree consequences. The citation
now names both and retains that qualification. The v2 metadata confirms
submission on 13 September 2026 and 41 pages; the PDF title date is
15 September, so the bibliography says “submitted.” Carletti's v1 and v2
abstracts and metadata support the limited inversion/linearization background
comparison; no full-text audit or exhaustive priority search was performed.
The bibliography distinguishes first submission in 2001 from the 2002 revision.
The delivered source audit remains historical evidence with its original bytes.

The baseline and revised PDFs each passed three LaTeX passes. The revised
report has 172 pages (previously 171), with the same three small overfull
boxes and one underfull box and no LaTeX/package warnings. The subsection
contents-number column now fits `26.10`, and the resonance heading stays
with its table. Forty-six physical pages covering the affected proofs,
summaries, tables, limitations and bibliography were visually inspected.
All 651 source labels retain their order; all 1,302 auxiliary numbering
fields are preserved (floating-label write order may change with pagination).
Of 149 standard statements, 146 are unchanged modulo whitespace; three
clarify the formal-case reference, supported exponent/Hahn label, and
rectangular-radius/parameter hypotheses. Source 10 contains 12 of those
standard statements. These are source inventories, not Lean coverage.

All 44 historical audit/code/data files remain byte-identical to the saved
baseline and `a99b4ee`. The unchanged source-10 verifier, which writes only
to stdout, was run with Python 3.13.14; its output matches the preserved
record byte for byte: 2,730 exhaustive colored trees, 18,466 marked-subset
checks, 1,000 seeded random checks, 21 nonzero denominator checks and eight
conjugacy/inverse component identities through parameter degree three and
spatial degree six. These finite exact checks do not establish the infinite
or analytic claims. The independent 49-source audit still checks 2,465
statements without issues, and all 2,726 cited source labels resolve.

The sync merged `43b8bad`, adding circle chords, directed and interior
inscribed angles and cyclic Ptolemy equality. No manuscript source changed.
The combined `LEAN_NUM_THREADS=2 lake build` passed 4,030 jobs; the default
axiom audit accepted 7,925 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. The independent inventory remains at
49 sources and 2,465 standard statements; all 2,728 cited source labels and
1,080 local Markdown destinations resolve. These incoming implementation
mappings remain distinct from the source-10 mathematical review.

## Nonlinear holonomic main-text review

The [holonomic report](surcomplex/holonomic-rigidity-for-entire-hahn-functions/)
review now covers source 10's Theorem D, Sections 14–17 and the corresponding
Section 19.3 limitations. Independent readings checked the elementary
coefficient-family algebra and scaled initial polynomial before the finite
exclusion certificate, first-order nondegeneracy, degree candidates, algebraic
solution locus, Riccati classifications, higher-order examples, positive-weight
Euler theorem and support-derived consequences. The later coefficient-field
proofs from sources 11 and 12 retain their separate pending review scope.

The family-algebra proof now explains why regrouping preserves finite
contribution at each exponent. Gauss multiplicativity identifies both the
minimum and its residue. The active polynomial is written as the finite sum
of the active coefficients' leading terms; distinct powers of the auxiliary
variable prevent cancellation. The example `1 − X + t^η X²` separates that
nonzero initial polynomial from evaluation at `X = 1`. The active-degree
proof gives a positive scale even with no low-index coefficients and no
divisibility or order unit.

The exclusion proof applies its own finite inequalities directly and explains
why every positive-valuation noncorner term has zero residue. Its cofinal
corollary treats `d_P = 0` before invoking the positive-degree certificate.
The corner target degree is explicitly nonnegative, despite the possibility
of negative shift. Clearing rational-function denominators is justified in
the formal Laurent field, without requiring a nonzero denominator at zero.
The nonuniform Riccati proof chooses `λ = δ + ε`, using just a positive
element of the nonzero group. The candidate-degree and solution-locus
arguments retain injective Hahn-field extension and exact finite-solving
hypotheses; the necessary candidate set is not claimed attained in full.

The higher-order proof now refers to the coefficient in its specified degree,
which may vanish by cancellation. An explicit unit multiplier changes a
nonzero corner to a zero corner while preserving exactly the constant formal
solutions. The degenerate example still gives only polynomial solutions of
unbounded degree, not a counterexample to polynomial rigidity. Positive Euler
weights bound each multi-index coordinate explicitly. The comparison with
finite mixed-derivative span describes different input criteria; on the
strongly entire class each criterion forces polynomials, which satisfy both.
The README's Euler summary now retains the essential nonzero-polynomial
hypothesis. The shared notation guide separates Gauss values from evaluated
values, residue from full-coefficient corners, and rational degree bounds
from value-group scales.

The source-10 repository comparison is now explicitly bounded by its historical
pin and named reports; the preserved audit does not support a blanket current
absence claim. The scalar Riccati and tail-span comparisons were checked
against their actual stated derivations, fields and function classes. The
current primary-source check read Hu–Luan v1's field hypotheses and Theorems
1.1, 1.3 and 1.5, adding the omitted characteristic-zero qualifier; Cano–Fortuny
Ayuso's initial/indicial definitions; Giansiracusa–Mereta's differential-norm
framework; and Mantova–Matusinski's normal-form discussion. Hayman's
bibliographic/introduction extract and Hu–Yang's publisher description were
checked at that limited scope. These are contextual precedents, not imported
proofs of the arbitrary-rank theorem; no full-book or priority audit is claimed.
Historical source audits and package records keep their original bytes.

The baseline and revised PDFs each completed three LaTeX passes; their final
logs have no warnings or box notices. The revised report has 90 pages
(previously 89), and 26 physical pages covering the source-10 body, front
matter and limitations were visually inspected. All 274 source labels retain
their order and numbering. All 81 standard statement environments and seven
principal theorems A–G are unchanged modulo whitespace; source 10 accounts
for 19 standard statements and Theorem D. The changes concern proofs,
examples and scope descriptions, without adding Lean coverage.

All 28 historical audit/code/data files match the saved baseline and
`c384738` byte for byte. The unchanged source-10 verifier was run on a copy
with Python 3.13.14; its full record matches the delivered JSON except for
Python 3.13.5 becoming 3.13.14. All 2,113 checks pass: 450 finite-Hahn
certificates, 240 first-order nondegeneracy checks, 480 higher-order corners,
500 ordered-group inequalities, 360 weighted-Euler identities and 83 worked
examples. These are finite checks, not proofs of the general support or
rigidity assertions. Before the sync, the independent inventory checks
2,465 statements in 49 sources; all 2,728 cited source labels and 1,083
local Markdown destinations resolve.

The sync merged `56f9aa6`, including polygon and triangle formalizations
from `f5d30b8` and the six-manuscript gamma/zeta assembly/catalogue from
`7af7056` and `087ee37`. The only changed LaTeX sources were the gamma/zeta
report and collection manifest; the holonomic review source is unchanged.
The gamma/zeta source now has 94 indexed standard statements in place of
the provisional base's 25, so the independently checked inventory has
2,534 statements in 49 assembled reports. Its main-text mathematical review
remains pending. All 2,802 cited source labels and 1,099 local Markdown
destinations resolve after the merge.

The combined `LEAN_NUM_THREADS=2 lake build` passed 4,034 jobs. The default
axiom audit accepted 8,010 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. This confirms the synced Lean target;
it does not formalize the nonlinear holonomic or gamma/zeta manuscripts.

The incoming implementation mappings and four new root imports were checked
against the polygon, spread and triangle-valuation source hypotheses. The
gamma/zeta integration check confirms 94 indexed statements and 222 unique
labels, with no mapped proof dependent on a replaced source label. All 29
historical code/data files (eight code/build files and 21 data files) remain
byte-identical to `c384738`, including the 738-byte CSV with 24 CRLF lines.
Corrected the new guide's blanket label-citation claim: neighbouring guides
and the ledger cite its labels, while Lean mappings remain absent. This is an
integration check, not the pending gamma/zeta mathematical review.

## Coverage reconciliation and the spectral singleton exception

The next sync merged `2bef7c0`, including the ten modules introduced by
`a754069`. All ten root imports occur exactly once, and the source labels in
the new mappings resolve. The merged target passed
`LEAN_NUM_THREADS=2 lake build`: 4,051 jobs and an axiom audit of 8,710
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
No manuscript source changed in this incoming merge.

The holonomic report's current status now includes integer, affine and
unit-orbit valuations, generic constant-point avoidance, inward stability
and torsion covariance. It also retains the already proved partial-theta
implications and distinguishes them from the pending converse implications
and full classifications. Section 13.3 records the remaining support,
closure, recurrence-conversion and generic-line dependencies. The title,
attribution table, conclusion and guide agree; the earlier review record
is explicitly historical. These updates record incoming Lean coverage and
do not prove the source-10 nonlinear or later coefficient-field theorems.
The updated report still has 90 pages after three LaTeX passes, with no final
warnings or box notices. All 88 result environments, 274 label numbers and
28 historical files remain unchanged. A rendered comparison with the
preceding review PDF found 54 changed pages (physical pages 1–2, 34–83 and
86–87); all were visually inspected, including the expanded dependency
subsection and the resulting text reflow. No layout defect was found.

The new row/column-finite algebra mapping exposed a source error in the
closing clause of `ihs:rf:prop:algebra`. Part II allows any nonempty index
set, so its unconditional zero-divisor assertion fails for a singleton:
then `R_I = ℂ` and `𝒜_rf = K` is a field. The source now asserts zero
divisors when there are two distinct indices, and proves it with the
nonzero constant matrix units `E_ii` and `E_jj`. Its other algebra, action,
involution and order-inequality claims retain the original hypotheses.
The ledger records the conditional Lean theorem and does not claim a
separately formalized singleton equivalence. This bounded correction does
not extend the main-text review to the Drazin/Fredholm additions.
Both baseline and revised PDFs passed three LaTeX passes at 97 pages, with
no warnings or overfull boxes and the same single underfull-box notice.
All 404 source labels and 808 AUX numbering entries are unchanged, as are
all 20 historical files. A rendered comparison of all 97 pages changes only
physical page 38; that page and its neighbours were visually inspected.

The root guide's exponential-profile summary now retains the ordered
exponential and nontrivial convex valuation assumptions. The ledger also
retains the coarsened unique-lift theorem's stabilization assumptions;
automorphisms preserving only the coarsened valuation ring remain pending.
The bounded-orbit mapping now acknowledges the proved exterior
non-preperiodicity clause, and the Markov summary names stochasticity.
The statement inventory remains 2,534 results in 49 reports; line anchors
were refreshed after the two source edits. All 2,851 cited source labels
and 1,120 local Markdown destinations resolve, and `git diff --check` passes.
These are scope and source corrections, not additional Lean declarations.

The final sync merged `9abc436`, including the seven triangle-defect and
relative-flatness modules from `ae0ec9f`. It changed no manuscript source.
The analysis guide's finite-lift label and the gamma/zeta guide's qualified
attribution labels were checked against the current sources. The gamma
merge resolution retains the 94-statement inventory and the distinction
between label citations and mapped Lean proofs. All seven imports occur
once, and the new rows' nine source labels resolve. The two mappings retain
the nonzero-vector and infinitesimal-angle hypotheses for the defect, and
the largest-side and relative-gap hypotheses for flatness, without assuming
comparable side scales. The normalized-coordinate flatness theorem remains
explicitly pending; this was a bounded mapping/scope audit.
The combined `LEAN_NUM_THREADS=2 lake build` passed 4,058 jobs, with the
axiom audit accepting 8,861 declarations and only the same three axioms.
The independent inventory remains 2,534 statements in 49 reports; all 2,858
cited source labels and 1,127 local Markdown destinations resolve.

## Coefficient-field holonomic main-text review

Reviewed sources 11 and 12's Theorems E–G, Sections 20–22, their examples,
and the corresponding introduction, README, notation and hypothesis audit.
The dependency order is the all-scale coefficient criterion, valuation-rank
inequality, principal convex bound and exterior obstruction; then formal
coefficient recovery, coarsening descent and the independence consequences.
This is a main-text proof review. Original-delivery reconciliation,
foundational imports beyond the targeted checks below and historical
priority remain separate obligations.

Expanded the product argument through finite coefficient convolution, so
cancellation cannot conceal an infinite set of low-valued product terms.
The valuation-rank proof now explicitly lifts a rational basis, covering
infinite cardinal ranks as well as finite ones. Corrected the definition
of coefficient-value rank: its dimension is a cardinal, while its span is
contained in the divisible hull. Normalizing an entire denominator,
reducing numerator and denominator together, and lifting the resulting
rational identity through the embedded coefficient field are now separate
steps. The rationality-descent lemma reduces its infinite linear system to
a finite spanning family of augmented rows, including denominator degree
zero. The formal-exponential example uses polynomial degrees, with no
analytic interpretation of a limit at infinity over an arbitrary field.

The coefficient theorem now clears rational denominators in its mixed case
and Laurent poles in its relative differential case. Its coefficient
extraction explicitly excludes every tail index beyond the target. The
cutoff `N_0 = θ + 2r` determines all multiplier coefficients from one fixed
prefix before the induction begins; the proof's prefix indexing now agrees
with its statement. The Laurent corollary explicitly retains characteristic
zero and explains why its triangular jet substitution preserves a nonzero
relation. The mixed argument uses only eventual nonvanishing of the
exponential-polynomial multiplier; no effective final exceptional index or
valuation estimate is inferred from Skolem–Mahler–Lech.

Added Corollary 22.9, `hol:cf:cor:meromorphicmixed`, as a consequence assembled
here from the two sources: without an order unit, every nonrational element
of the fraction field of strongly entire series has independent mixed jets
at dilations with no root-of-unity quotient. Multiplication by a power of
`z` removes a Laurent pole. Completing each finite block of jet orders makes
the Leibniz substitution an invertible triangular change over `𝕂(z)`, so a
nonzero relation remains nonzero. Finite coefficient generation, the rank
and convex bounds, and fraction-field descent would then force rationality.
Neither delivered source states this corollary, and no priority or Lean
claim is made for it. Its exclusion is rationality, not polynomiality.

Added the concrete formal series `F + 1/(1−z)` to illustrate the rank
criterion's nonconverse. Every coefficient has value zero, while subtracting
`1` recovers infinitely many independent monomials. Its mixed jets differ
from those of `F` by rational functions, so the same independence survives;
it is not strongly entire. Expanded the private-prefix argument for the
continuum family, including a single selected branch and denominator
clearing over the other branches' coefficient fields. Replaced wording
about derivatives "at powers of q" by the actual formal series, keeping
point values distinct from function independence.

The summaries now distinguish universal rigidity without an order unit from
individual infinite-coefficient-rank examples in rank one. Uncountable
cofinality makes the nonpolynomial entire assertions vacuous, not the
criterion for arbitrary formal series. The hypothesis audit distinguishes
nonnegative derivative orders from integer dilation powers, power series
from Laurent and multivariable series, and a single nontorsion dilation from
pairwise non-root-of-unity quotients (which allow the parameter `1`).
Historical delivery audits keep their original bytes.

The current external check read Bell's classical SML statement in
[Theorem 1.1, version 2](https://arxiv.org/pdf/math/0501309v2), rather than
importing his affine-variety generalization. The targeted source comparison
also checked the LKU recurrence antecedent in its publisher PDF, the normal
form statements of Bournez–Guilmant Corollary 2.7 and Mantova–Matusinski
Section 2.2, and Hu–Luan's characteristic-zero hypothesis, now restored in
this second comparison paragraph. Hurwitz and Lech were checked only through
primary metadata and the inspected modern attributions; the arithmetic and
D-algebraic framework papers only at the stated contextual scope. The
repository comparison remained limited to its historical pin and named
neighbours. No exhaustive source or priority search is claimed.

Baseline and revised PDFs each passed three LaTeX passes, at 90 and 91 pages,
with no final warnings or box notices. All 33 pages with changed text or
pagination were visually inspected, together with the unchanged transition
page 62: 34 revised physical pages in total (2–3, 7 and 58–88), with no
layout findings. The baseline contents page was also compared. All 274 earlier
labels retain their numbers; the new label is Corollary 22.9. Of the original
88 result environments, 87 are unchanged and the remaining one only makes the
characteristic-zero coefficient-field assumption explicit. The new corollary
brings this report to 82 standard statements plus seven main theorems, and
the independent 49-report inventory to 2,535 standard statements.
All 28 historical files remain byte-identical. Both unchanged source
verifiers were run on copies: source 11 passes 8,673 finite cases with
SymPy 1.14.0, and source 12 passes 9,308 checks using the standard library.
Their complete records differ from the delivered records only in Python
3.13.5 becoming 3.13.14. These finite checks do not prove the general
coefficient-field, descent, independence or new meromorphic assertions.

### Validation after the triangle merges

Merged `7da84a2`, which adds the normalized-coordinate flat-triangle theorem
and aligns the row/column-finite spectral comments with the corrected
two-index zero-divisor hypothesis. Its seven new modules are each imported
once. A bounded mapping audit checked every normalized-triangle clause and
confirmed that the singleton algebra equivalence remains explicitly pending.
The combined `LEAN_NUM_THREADS=2 lake build` passed 4,065 jobs, with 9,011
declarations accepted by the default axiom audit.

The next fetch brought `a73c1b4`, adding six imported modules for the symmetric
height and side-gap triangles and the appreciable-gap degeneration. Each
module is imported once; the bounded scope audit confirmed every clause of
the three full-example mappings, including complete strong sums, the
collinear standard-part shadow and the actual ordinal-omega equivalents.
Neither incoming change altered a manuscript source. After merging it, the combined
build passed 4,071 jobs, with 9,219 declarations accepted by the axiom audit;
both builds use only `propext`, `Classical.choice` and `Quot.sound`.
The independent inventory remains 2,535 statements in 49 reports; all 2,864
cited source labels and 1,141 local Markdown destinations resolve. The new
coefficient-field corollary remains a source-level result pending Lean
formalization.

## Drazin spectral main-text review

Reviewed Part III, Sections 28–37, of the infinite-dimensional Hahn spectral
report in dependency order: finite-index Drazin identities, Laurent
recurrences, strong parameter straightening, cyclic-support projection,
inverse descent, halos and valuations, then Banach consequences, ramified
polynomial mapping, examples and surreal specialization. The 19 numbered
Part III results retain their statements and hypotheses. This review does
not cover Part IV's Fredholm proofs or complete the remaining imported-result,
original-source reconciliation and priority obligations.

Expanded the complementary-idempotent calculation, distinguished the
idempotents from the elements in their corners, and proved why minimality
of the Drazin index forces the leading nilpotent coefficient to be nonzero.
The Laurent converse now displays the annihilation calculation that supplies
the second Drazin identity. Added a lexicographic support example explaining
why general Hahn series can have infinitely many negative exponents even
though restriction to a positive cyclic subgroup has a finite Laurent tail.
The existing straightening proof was checked through its strong inverse
and finite-word bookkeeping, without a cofinal-powers assumption.

Made the local resolvent convention `(S − u1)⁻¹` explicit, including the
sign change for the opposite convention. The local polynomial germ and its
formal inverse preserve the valuation of every nonzero infinitesimal,
making the auxiliary root displacements explicitly nonzero before inverse
descent is applied. The finite-pole profile now computes in Riesz corners
with identity `P_a`, handles a zero complementary corner and retains the
nonempty spectral fibre. Summaries distinguish the Drazin index from
ramification, zero from positive valuation, the normal-case corollary from
the general halo theorem, and analytic Banach interpretations from the
arbitrary-algebra results. The hypothesis ledger now records the ordinary
norm estimates used by the examples.

Corrected Volterra's exact range description to require an absolutely
continuous representative with value zero at the origin and derivative in
`L²`. Corrected the lexicographic squaring-image description to include zero.
Extended the increasing-Jordan-block example's fixed-vector obstruction from
monomial displacements to every nonzero infinitesimal `ε`. In block `n`,
the finite inverse has leading exponent `−n v(ε)` and nonzero leading vector
`−lc(ε)^(−n) 2^(−n²) e₁`; earlier terms have larger valuation. Any global
solution would therefore have an infinite descending support. At zero the
operator has a kernel, and away from the monad its algebra inverse is a
bijection, so its vector and algebra spectra both equal the whole monad.
The delivered block calculation used a monomial; this is a deduction added
in the review, independently checked, and still pending in Lean.

Targeted primary checks read Boasso's
[Drazin-spectra manuscript](https://arxiv.org/pdf/1307.6942), Theorem 12's
pole/accumulation dictionary, and his
[Banach-algebra manuscript](https://arxiv.org/html/1309.5025v1), Theorem 2.1's
empty-spectrum/algebraicity equivalence. Koliha's
[publisher text](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/85E8C5B0B219A97713440CAB90B7C73F/S0017089500031803a.pdf/generalized_drazin_inverse.pdf),
Definitions 2.2–2.3 and Theorem 4.2, confirms the distinct generalized notion;
its Laurent-resolvent convention also explains the sign clarification.
These are checks of the named imports, not a renewed exhaustive literature
or priority search. The historical audit records remain unchanged.

Baseline and revised PDFs each completed three LaTeX passes, at 97 and
98 pages. They have the same single pre-existing underfull notice in the
novelty table, with no new diagnostics. All 93 standard result statements,
404 source labels and their numbers, and 20 historical code/data/provenance
files are unchanged. The unchanged Part III verifier ran on a copy and
passed 484 exact finite checks; its full JSON differs from the delivered
record only in Python 3.13.5 becoming 3.13.14. Those checks do not establish
the general support, spectral or strengthened vector assertions. The
49-report inventory remains 2,535 standard statements; line hints were
refreshed without adding a Lean mapping.

All 24 pages with changed text or pagination were rendered and visually
inspected: revised physical pages 6–8, 13, 15–17, 57–71 and 94–95. No layout
issue remains, and the report README's 15 Part III numbered references match
the final auxiliary file. A final consistency edit qualifies the standing
Banach-norm summary as applying to the general results; another three-pass
build preserved every page except physical page 57's wording, and that page
was inspected again. This comparison used extracted text and pagination,
not a claim of pixel equality for other pages.

Merged `2bd87f6`, including the reciprocal-leg and thin-triangle hierarchy
formalizations in `5e67a5b`. A bounded source/declaration audit confirmed
both full-example mappings, all five unique new imports, and the added
relative-asymptotic lemmas. No manuscript source changed in the merge.
After the first build process terminated without a proof error, a fresh
incremental `LEAN_NUM_THREADS=2 lake build` completed all 4,076 jobs.
The default audit accepted 9,427 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. All 2,866 cited source labels and
1,148 local Markdown destinations resolve; the independent inventory still
has 2,535 statements in 49 reports. The Drazin source improvements add no
Lean coverage.

## Fredholm spectral main-text review

Reviewed Part IV, Sections 38–48, of the infinite-dimensional Hahn spectral
report in dependency order: analytic identity lifting, the compact range
defect, Riesz projections and direct rotation, finite Hermitian clusters,
the main classification, the unitary obstruction, trace and determinant,
finite coupling and the coherent analytic boundary, then higher-rank
examples. Independent checks of the determinant chain and counterexamples
found no failure under the stated hypotheses. The abstract now explicitly
requires infinite-dimensional separable `H` for the compact-spectrum
formula; finite-dimensional injective residues do not have its whole monad.
The comparison table now says perturbations need not commute with `T`,
which includes commuting perturbations and zero.

Section 44's determinant and Fredholm alternative use fewer hypotheses
than the compact-spectrum classification. Their scope now allows any
ordinary complex Hilbert `H` and any set-sized ordered abelian `Γ`, including
`H = 0` and `Γ = 0`, without divisibility, self-adjointness or a compact
residue. The proof needs finite-word support, the ordinary trace-class
Fredholm alternative and finite linear algebra over the Hahn field, with
no scalar root extraction. This is an independently checked extension of
the written source, **Pending** in Lean. The subsequent compact-spectrum,
finite-coupling and no-characteristic applications retain their stated
hypotheses. Summaries and the shared notation guide distinguish these scopes.

Two displayed standard statements have explicit typing clarifications:
`ihs:fr:prop:detidentities` names a fixed Hilbert conjugation for operator
conjugation, while the canonical adjoint identity is separate;
`ihs:fr:lem:correction` requires bounded finite-rank factors. The other
91 displayed standard statements are textually unchanged, but Section 44's
broader hypotheses change the effective scope of its results. No Lean
implementation mapping is added or extended.

Expanded the finite-direction Taylor argument and the contour's ordinary
resolvent bound, without assuming a common neighbourhood for all clusters
or all coefficient directions. Gave the direct rotation's constant term,
the zero-dimensional Hermitian case, and explicit cluster kernel/cokernel
maps. The exterior-power bound proves the determinant is an entire map
on the trace-class Banach space; the rectangular finite-rank identity is
derived from finite linear algebra. The Fredholm proof now types the
Sylvester lifting in `B(C^m,H)`, allows negative exponents in the finite
matrix inverse, and gives both induced quotient maps and their composites.

The counterexample now also excludes a common complex disc of labelled
analytic eigenvalues: the ordinary operator norm and Cauchy's estimate
would uniformly bound their second coefficients, contradicting the computed
growth. Trace-norm convergence and Cauchy's formula justify convergence of
every fixed finite-section determinant coefficient, separate from the
divergent product of the infinite operator's labelled branches. Corrected
the reciprocal-coupling sentence to exclude `z=0`. Expanded the coherent
nonvanishing argument with the identity theorem and an explicit monomial
beyond its threshold, and retained the precise lexicographic exponents in
the repeated-residue example.

Targeted primary checks verified Kato's direct-rotation formula as recalled
by [Simon, Equation (4)](https://arxiv.org/pdf/1703.05437), the exterior-power
determinant inputs and trace-norm perturbation estimate in
[Bornemann, Section 3 and Equation (4.1)](https://arxiv.org/pdf/0804.2543),
and arbitrary-rank Hahn algebraic closedness in
[Poonen, Corollary 4](https://math.stanford.edu/~conrad/Perfseminar/refs/poonencomplete.pdf).
The stronger Banach-space analyticity and rectangular identity are explained
in the article rather than attributed as explicit statements of Bornemann.
These checks do not renew a priority search or exhaust the remaining
foundational imports and original-source reconciliation.

Baseline and revised PDFs each completed three LaTeX passes, at 98 and
99 pages, with the same single underfull notice in the novelty table and
no new diagnostics. All 404 source labels and their numbers are preserved;
the report has 93 standard results, including Part IV's 21. All 20 historical
code, data and provenance files are unchanged. The copied Part IV verifier
passes 1,268 finite checks with Python 3.13.14 and SymPy 1.14.0; its JSON
differs from the historical record only in Python version, elapsed time and
timestamp. These finite checks do not establish the infinitary assertions
or the broader determinant/Fredholm scope.

All 36 pages with changed text or pagination were rendered and visually
inspected: revised physical pages 2–3, 6–8, 10–20, 72–87 and 93–96. No layout
issue remains. A final interface consistency edit was followed by another
three-pass build; the affected interface pages were inspected in that build,
and the other inspected page images were unchanged. The README's ten Part IV
numbered result references match the final auxiliary file. The independent
inventory still has 2,535 standard statements in 49 reports; all 2,866 cited
source labels and 1,149 local Markdown destinations resolve. This review
changes source exposition and scope, with no new Lean coverage.

Merged `cb479fe`, including `f6fe627`'s amplitude-intersection and signed
tangency formalizations. A bounded source/declaration review confirmed all
seven new root imports and the three new mapping rows, including the signed
error estimate and the tangent example's positive-infinitesimal parameter;
SSA reconstruction remains pending. No manuscript or historical artifact
changed upstream. The combined `LEAN_NUM_THREADS=2 lake build` passed all
4,083 jobs, and the default audit accepted 9,588 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. After merging, all 2,872 cited
source labels and 1,156 local Markdown destinations resolve; the inventory
remains 2,535 standard statements in 49 reports.

## Field-automorphism main-text review

Reviewed Sections 1–15 and Appendix B of the field-automorphism report in
dependency order: real-axis stabilizers and norm/circle rigidity, support
control, monomial and coefficient-motion constructions, valued and additive
decompositions, topology and derivatives, class homogeneity and real forms,
then exponential rigidity and the stated applications. Independent readings
of Sections 7–11 and the class arguments found no false theorem under the
stated full-field hypotheses. This review does not complete original-source
reconciliation or certify historical priority.

Corrected the rational-cut explanation to refer to irrational ordinary reals;
rationals are fixed already, and real algebraic constants are fixed by their
polynomial and order data. Clarified that a strong field map is determined
by both coefficient and monomial images. Strongness alone does not remove
coefficient data: the Taylor motions fix every monomial but move constants.
Defined strong additivity for general additive maps, so its use for the
fixed-shift derivation is explicit. Added the coefficient-motion valuation
bound, the automatic identity `d(i)=0`, the correctly reindexed character
in the valued factorization, and the rational-comparison proof of the
additive decomposition's leading coefficient. Corrected the Cayley comparison
to exclude division by zero and give the missing `x=0` value separately.

The finite-observation non-density proof now names `Aut(No)` and then proves
the assertion for all `Aut(K)`: fixing `t` sends each rational power to that
power times an ordinary root of unity, so a strong image of the chosen sum
cannot acquire its new `ω`-exponent. This is an added source-level argument,
still pending in Lean. The derivative theorem now excludes every `K`-valued
derivative for `0<a<1`, removing the ambiguous word “finite.” Its proof uses
an explicit increment beyond any proposed valuation threshold, without a
set-indexed cofinal net. Injectivity justifies the inverse derivative's
punctured limit and the failure of local constancy.

Class-map collections, pointwise fixed-field predicates, and finite indexed
actions now have distinct foundational interpretations. The back-and-forth
proof fixes a set-like global well-order, makes both extension steps at each
successor, and defines its class graph from compatible set-length recursions.
The finite-group theorem is reduced to ordinary algebraically closed,
invariant set subfields containing witnesses for faithfulness. Directed
unions of their real fixed fields give the class real form; the explicit
two-coordinate identity gives its complexification. The real closure of
`No(T)` uses unique compatible ordered embeddings and least representatives
of stage-element pairs, avoiding proper-class equivalence classes as elements.
The set-cut conjugacy criterion retains both empty cut sides.

The generic exponential proof now identifies the image of `w ∘ E` with
`w(Fˣ)`, without silently assuming surjectivity onto a larger codomain.
Current generic `ExponentialProfile` proofs are distinguished from dedicated
`saut:` mappings and from the actual surreal exponential instantiation.
The older `SigmaDerivation` ledger row now points to the later generic
ordered results instead of incorrectly listing them as pending. No new Lean
code or implementation mapping is introduced by this review.

Targeted primary checks inspected the four-factor decomposition in
[Kuhlmann–Serra, Theorem 3.7.1](https://arxiv.org/html/2107.03362v3), and the
kernel/skeleton decomposition and canonical lifts in
[their Hahn-group paper, Section 3.2](https://arxiv.org/html/2302.06290v2).
The ordinary Puiseux input is stated in the introduction of
[Paran–Vo](https://arxiv.org/abs/2311.17544); real closedness follows by
complexification. [Conrad, Theorem 3.1 and Section 4](https://kconrad.math.uconn.edu/blurbs/galoistheory/artinschreier.pdf)
supplies the set-field Artin–Schreier input, while
[Hamkins's global-choice equivalences](https://jdh.hamkins.org/the-global-choice-principle-in-godel-bernays-set-theory/)
justify the set-like global well-order. The manuscript supplies the passages
to its class setting. These checks do not re-audit the pinned KKS questions
or establish a complete external-literature review.

Validation against `076b1fa`: three LaTeX passes produced a 37-page PDF
without diagnostics; all 37 rendered pages were inspected for layout.
All 86 source labels and their result numbers are preserved. Of the 26
standard statements, only `saut:thm:zeroderiv` changes wording, as described
above. The installed PDF matches the compiled source. All 2,872 cited source
labels resolve, and the inventory still contains 2,535 standard statements
in 49 reports. No verification code or data accompanied this report.

Merged the subsequent formalization commits through `71e9606`; they change
Lean code, the root imports and coverage documentation, but no manuscript
sources. The ledger conflict keeps both the newly completed Prony mappings
and the corrected `ExponentialProfile` status. Checked the assumptions and
main declarations of the incoming `LogModulusClassification` and
`ComplexValuationKernel` modules against their mappings, then updated both
automorphism READMEs and the field-automorphism article. These generic
results require an explicitly injective `OrderedExp`; the kernel also uses
a nontrivial convex valuation. The separate `L`-automorphism predicates,
relational treatment of coarsening and pending actual surreal instantiations
are now explicit. This integration check is not a mathematical review of
every incoming Lean module.

The updated article again passes three LaTeX runs without diagnostics and
retains 37 pages, all 86 labels and every result number. Inspected all 29
pages whose extracted text or pagination changed after the coverage update.
The report README's result references agree with the compiled numbering;
its Taylor-motion summary now states the real-preservation condition.

Combined validation: `LEAN_NUM_THREADS=2 lake build` passed all 4,264 jobs.
The axiom audit passed for 12,648 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. All 3,016 cited source labels and 1,253
local Markdown destinations resolve. The independent inventory remains
2,535 standard statements in 49 reports, and `git diff --check` passes.

## Omnific Diophantine geometry: elementary algebra and source integration

The [Diophantine article](surreal/omnific-diophantine-geometry/article.tex)
now has a Sections 1–4 main-text review and a
[source reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md)
for the elementary algebra in companion manuscripts 02 and 05, recovered
from the archives in `f0b7f43`. This extends base 01 with four results:
a common set-sized Hahn workspace, mixed gcds with an ordinary integer,
a nilpotent-image test, and a common multiple of every ordinary power in
a set-sized family. Their proofs use support localization, ordinary Bézout,
idempotence of the infinite-part ideal, and monomial clearing respectively.

The exposition distinguishes the constant-coefficient kernel in the real
and complex rings, its failure to preserve order, its difference from
standard part, and the reversal between growth degree and valuation.
Quotients by class ideals are explained through congruence maps; completion
systems use ordinary residue rings. The common-divisor and clearing arguments
explicitly allow enlargement of the input exponent group. The shorter
`√2` witness to failure of integral closure supplements the base witness.

All 77 base labels are preserved with the prefix `odg:`; all 41 original
standard statements are unchanged after this renaming. The four additions
bring this article to 45 statements. Sections 5 onward are byte-identical
apart from the prefix changes; their proof review and source comparison
remain pending. The README now uses actual build and verifier paths,
and historical delivery scripts and outputs remain unchanged.

Validation: three pdfLaTeX passes produce a 31-page article with no final
warnings or over/underfull boxes. The three preserved SymPy 1.14.0 verifiers
pass; outputs match the delivery except for Python version metadata in
sources 01 and 02. Those finite checks do not establish the new general
support arguments. The independent inventory now has 2,614 standard
statements in 51 sources (1,026 theorems, 519 lemmas, 561 propositions,
508 corollaries). All 31 article pages and the eight changed catalogue pages
were visually checked. The catalogue remains 28 pages with no diagnostics;
its other pages have unchanged extracted text and pagination. All 1,287
local Markdown destinations resolve. This update adds no Lean coverage.

The synchronization through `6fbb985` imports the completed cosine-fold
multiplicity proofs and coupled-angular roots, rank-four algebra and
Jacobian/reality clauses. No manuscript source changed in that merge.
`LEAN_NUM_THREADS=2 lake build` passes all 4,280 jobs; the axiom audit passes
12,934 declarations with only `propext`, `Classical.choice` and `Quot.sound`.
All 3,101 cited source labels and 1,295 local Markdown destinations resolve;
the independent inventory remains 2,614 statements in 51 sources.
Final inspection also made the nonzero ordinary-modulus hypothesis explicit
in the introductory quotient notation and shared guide. The rebuilt article
still has 31 pages and no diagnostics; only physical page 5 changed, and
it was visually checked again. `git diff --check` passes.

## Synchronizing the expanded omnific article

The publish retry encountered the three-source assembly `bbdd536` and
additional manuscript placement `cf350b1`, merged remotely in `ed2039f`.
The expanded article is retained in full. Its 67 standard statements are
unchanged by this synchronization apart from added label aliases. All 81
labels of the preceding elementary review resolve among 159 unique labels;
nine now identify combined or renamed statements, as the reconciliation
explains. The independent review boundary is the shared elementary algebra
and the added univariate, CRT, prime-adic and general no-gcd arguments in
Sections 2–4. The expanded later proofs, the cited universal quotient and
remaining foundational/source work are not certified by this merge.

The incoming notation identified the nonnegative-growth support ring with
“nonpositive valuation”. This is false: `ω + ω⁻¹` has negative valuation
but a forbidden growth exponent. The corrected text requires the entire
support condition. The merge also restores explicit class-quotient
representatives, completion transition maps and the nilpotent proof via
finite products, and specifies the integer constant coefficient in `Oz_H`.
The claim excluding a universal common multiple now explicitly excludes
zero. The guide adopts the expanded article's `Π` notation, and the README
no longer claims that the previously indexed base was a new unreferenced
report or that the sibling already contains an assembled source-05 proof.

The newly placed local manuscripts 06–07 (Diophantine), 12–16 (quotients)
and 10 (entire-function rectification) remain supplementary artifacts,
not main-text integrations. The quotient source is still base 06, with
twelve companions assigned. The reader map and catalogue now distinguish
that placement from the assembled sources 01, 02 and 05. The current
inventory is 2,636 standard statements in 51 sources (1,035 theorems,
525 lemmas, 564 propositions, 512 corollaries), with separately styled
claims still in scope. No extra Lean coverage is implied.

Merge validation: three clean pdfLaTeX passes produce the 55-page article
and 28-page catalogue. All article pages and the 23 catalogue pages whose
text or pagination changed were visually checked; the final zero exclusion
changed only article page 51, checked again. All 3,124 cited source labels,
1,297 local Markdown destinations and the independent 51-source inventory
pass. The original three verifiers are unchanged and their passing runs
above remain applicable. This incoming merge changes only documentation,
so the successful 4,280-job Lean build and 12,934-declaration axiom audit
remain applicable. `git diff --check` passes.

A second publish retry merged `9a385d3`, including the coupled local-algebra
proofs in `04c93de` and an independent refresh of the same Diophantine index.
The conflict resolution retains the expanded article's reviewed labels and
placement boundaries while preserving all incoming Lean mappings. No
manuscript or PDF changed in this second merge. The combined
`LEAN_NUM_THREADS=2 lake build` passes all 4,285 jobs; the audit passes
13,003 declarations using only the three permitted axioms. Source-label and
inventory checks still pass, and all 1,301 local Markdown destinations
resolve. The angular transport of algebraic multiplicities remains pending
in the incoming coverage mapping.

## Omnific transfer and rigidity review

The next pass reads Sections 5–7 of the expanded
[Diophantine article](surreal/omnific-diophantine-geometry/article.tex):
equational and positive-existential transfer, the Smith and ordinary-right-hand-side
criteria, constant products and decomposable fibers, binary/Pell/conic/norm
rigidity, local Euler derivations, separated powers and unimodular Fermat.
The Euler, separated-power and Fermat arguments were compared with the
recoverable source-05 manuscript. Exhaustive source reconciliation for the
other Sections 5–6 claims and verification of imported classical theorems
remain separate obligations.

The direct divisibility identity added during assembly omitted the hypothesis
that the derivation kills its coefficients. The corrected statement requires
`∂a = ∂b = 0`, displays the missing terms when this fails, and explains why
`∂c = 0` holds for the chosen Euler derivation. The proof of separated-power
rigidity therefore remains valid. Its leading-degree, quotient-ring and
binary-factor arguments also prove the complex version over `B_C`; the
one-variable prerequisite is extended likewise, with explicit attribution
of the archived real statements. No new standard result is added.

The proof explanations distinguish the real kernel from the complex kernel,
include the zero case of Pell descent, define norm-polynomial evaluation
without embedding a number field into `No`, and give a zero-row obstruction
to replacing Smith compatibility by constant-term compatibility. A rational
functional on `Q + Q√2` illustrates why one fixed Euler derivation need not
detect every nonconstant. The notation guide and article both state the minus
sign under `t = ω⁻¹` and distinguish this local construction from the normalized
surreal derivation. The Fermat proof makes the workspace containing the
unit-ideal witness explicit and explains why its divisibility quotients must
have nonnegative support. Its integer-coordinate consequence now explicitly
requires all three coordinates to be nonzero.

Validation preserves all 67 standard results, all 159 unique source labels,
and all label numbers. Four standard statement texts change: the two complex
extensions, the scalar-prefactor wording for decomposable equations, and the
Fermat nonzero-coordinate wording. Main Sections 8–14 remain byte-identical;
the appendix records the coefficient correction and updates the scalar
notation. The article has a clean three-pass 56-page PDF; the catalogue has
a clean three-pass 28-page PDF. Changed pages were visually checked.
The source-05 SymPy 1.14.0 verifier passes with output identical to its
preserved delivery record. Separate finite symbolic checks pass for all 36
pairs `2 ≤ m,n ≤ 7`, both with constant coefficients and with the full
derivative error terms; these do not certify the arbitrary-support proofs.
The statement-index and source-label audits pass, local Markdown destinations
resolve, and `git diff --check` passes. This is a documentation-only change;
it adds no Lean coverage. Sections 8 onward, remaining imported results,
source reconciliation and the placed companions remain on the review queue.

Synchronization merged `04a5b88`, adding the verified centered-sine formal
coordinate automorphism and transport of the coupled angular defining ideal
to a monomial formal quotient. Its numeric local dimensions and resulting
angular total multiplicity remain pending, as the incoming ledger states.
No manuscript or PDF changed in this merge. The combined
`LEAN_NUM_THREADS=2 lake build` passes all 4,290 jobs, and the axiom audit
passes 13,135 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. The source-label and 51-report inventory audits still pass,
and all 1,308 local Markdown destinations resolve.

## Omnific quadratic levels and bounded geometry

The next pass reads Sections 8–9 of the
[Diophantine article](surreal/omnific-diophantine-geometry/article.tex),
comparing source 01's quadratic classification, transvection, positive-bound,
orthogonal, symmetric-matrix and leading-homogeneous proofs, and source 02's
bounded-set and nilpotent-isometry arguments. It makes the polarization
`q(x) = B(x,x)` explicit, including half-integral mixed coefficients, and
expands the isotropic spanning and nondegenerate-complement construction.
The free isometry parameter is distinguished from the fixed infinitesimal
monomial used to reverse exponents. The notation guide also distinguishes
this quadratic normalization from Hahn–Tate's energy with a factor `½`.

The inverse matrix formula gives an additional consequence: along the
quadratic orbit, the coordinate ideal equals the starting integer tuple's
ordinary gcd ideal. Primitive integer points therefore yield unimodular
omnific families. The degenerate affine family also has proper-class size.
The definite-form argument extends finite integer isometry groups beyond the
standard Euclidean signed-permutation case.

The bounded-set proof previously passed from truth in `No` to a small field
without spelling out what happens to quantifiers. The expanded argument
constructs set-sized real closed subfields and proves agreement by induction
on finite ordered-ring formulas: an existential witness lies in a larger
set-sized field, and model completeness descends the assertion. The classical
inputs were checked against [Marker, Theorem 3.5 and Proposition 4.1](https://library.slmath.org/books/Book39/files/marker.pdf),
now cited in the bibliography. The proof applies the ordinary theorem only
between set-sized fields. It does not verify the imported real-closedness of
`No` or the normal-form foundations.

Empty definite levels, the explicit positive coordinate bound and zero-size
matrices are handled explicitly. A nonsymmetric nilpotent matrix with an
infinite entry shows why a constant characteristic polynomial alone gives no
entry bound. Two equivalent polynomial systems with different top-form zero
sets show why the leading-homogeneous criterion concerns the displayed
generators. Their elementary identities were checked symbolically.

All 67 standard results, 159 labels and label numbers are preserved. Only the
bounded-set statement's wording changes, to specify the ordered-ring language;
its scope is unchanged. Main Sections 10–14 remain byte-identical. The article
and catalogue have clean three-pass PDFs of 57 and 28 pages, respectively;
changed pages were visually checked. The source-01 and source-02 SymPy 1.14.0
verifiers pass, differing from delivery output only in the Python version
(3.13.5 versus 3.13.14). Source-label, full statement-index and local Markdown
link audits pass, as does `git diff --check`. No Lean source or coverage is
added by this review. Sections 10 onward, remaining imports, source
reconciliation and the placed companions remain pending.

Synchronization merged through `f6e031a`: `42c920e` completes the coupled
angular multiplicities using native formal-quotient dimensions, and the later
commit proves nonmonic simple-residue-root lifting in the actual finite
surreal and surcomplex rings. The latter does not assert lifting inside the
omnific ring; its domain is the finite valuation ring. The incoming ledger
retains the pending multivariate and actual support/first-coefficient
obligations. No manuscript or PDF changed in this merge. The combined
`LEAN_NUM_THREADS=2 lake build` passes all 4,295 jobs; the axiom audit passes
13,232 declarations with only the permitted three axioms. All source-label
and statement-index checks still pass, and all 1,314 local Markdown
destinations resolve.

## Omnific definability and induction

The omnific Diophantine proof review now reaches Section 10. Source 01's
Pell residue table and five-auxiliary guard were compared with source 05's
four-square definition, constant-term formula and failed induction instance.
The Pell index and unboundedness claims refer explicitly to ordinary
integers, and the guard proof supplies an ordinary bound for every witness.
The divisibility proof now gives the explicit obstruction `k = |ct(j)| + 1`
when `ct(j) ≠ 0`, and explains why the definition is a single ring-language
formula rather than an externally indexed infinite conjunction.

The induction discussion specifies the nonnegative domain throughout.
The order-free remark now supplies a formula in `{0,1,+,·}` whose witnesses
also lie in the nonnegative semiring; it defines precisely the ordinary
naturals there. This proves failure of an arithmetic induction instance
without an extra dependency on formalizing Lagrange's theorem inside Peano
arithmetic. The open-induction proof spells out why the workspace floor
stays inside its support group, and why quantifier-free truth, base case,
successor implication and a proposed counterexample transfer to that
set-sized workspace. No first-order theorem is applied directly to a proper
class as if it were a set-sized model.

Imported theorem statements were checked against the
[AFP three-square entry](https://isa-afp.org/entries/Three_Squares.html), the
pinned Mathlib `Nat.sum_four_squares`, and
[Glivická–Glivický, Sections 2.1, 2.3 and Theorem 1](https://arxiv.org/html/1701.02001).
The last reference is added to the bibliography without renumbering earlier
citations. The surreal normal-form and Hahn-field real-closedness inputs
remain separate imported obligations.

All 67 standard statements, 159 labels and label numbers are preserved;
main Sections 11–14 are byte-identical. Clean three-pass builds produce the
58-page article and 28-page catalogue, with all 28 changed article pages and
the changed catalogue page visually inspected. Source 01's SymPy 1.14.0
verifier passes (only its recorded Python version differs); source 05's
output matches its delivery record exactly. All 2,636 indexed results in
51 reports, 3,124 cited source labels and 1,314 local Markdown destinations
pass their audits. No Lean source changes or new Lean coverage are asserted.
Later proofs, source reconciliation and unintegrated companions remain
pending.


## Omnific projective directions and finite-support arcs

The Section 11 proof review compares source 01's lifting, Pythagorean and
rational-direction arguments, source 02's homogeneous clearing and signed
existence theorem, and source 05's finite ordered specialization and arc
theorem. New examples make two boundaries concrete: extracting the leading
coefficient vector can lose a positive coordinate, and a nonzero homogenizing
coordinate need not give an omnific affine ratio.

The rational-direction theorem has a stronger explicit consequence. Given an
ordinary gcd-one representative `m`, every omnific representative is `s m`;
an integer Bézout identity puts `s` in `Oz` and identifies the coordinate
ideal as `s Oz`. Primitivity forces `s = ±1`. Thus every primitive omnific
representative of a real projective point is an ordinary coprime integer
tuple. This does not equate primitivity and unimodularity for arbitrary
omnific tuples. The notation guide records that distinction.

The finite ordered specialization proof now establishes rationality of a
minimal-support convex combination by independent augmented integer
columns, and obtains strict separation from a closest point to zero. These
steps take place in ordinary finite-dimensional real space. The arc theorem
is extended from integer to real system coefficients, with auxiliary
expressions explicitly restricted to real coefficients: the group-algebra
map fixes those scalars. Its possible kernel is illustrated by a map on
`ℤ + ℤ√2` that preserves a chosen finite exponent list but kills an
unrequested expression. Equalities always survive; nonvanishing and signs
are protected by the chosen finite list. Substitution at `ω` proves the
finite-support converse, while positive purely infinite parameters retain
the prescribed signs. Including finite-support Bézout witnesses produces
unimodular families; no finite-support claim is made for arbitrary witnesses.

The article retains 67 standard results and all 159 labels and label numbers.
Only `odg:thm:specialization` changes its standard-statement text, with the
coefficient extension and clarification above; main Sections 12–14 are
byte-identical. Article and catalogue compile cleanly in three passes to
59 and 28 pages; all 24 changed article pages and the changed catalogue
page were visually inspected. Source-01 and source-05 SymPy 1.14.0 checks pass, with only
source 01's recorded Python version differing from delivery. Inventory,
source-label and local-link audits pass for 2,636 results in 51 reports,
3,124 cited labels and 1,314 local destinations. The new general arguments
are source proofs, not assertions established by those finite scripts.
No Lean source or coverage is added. Later proofs, imported foundations,
source reconciliation and unintegrated companions remain pending.


Synchronization merged through `173eb52`, including `2008172`'s actual
surreal polynomial root stability, both valuation error bounds and uniqueness
throughout the open neighborhood. The incoming ledger correctly keeps the
trigonometric chart, angular transport and sharpness examples pending; no
manuscript or PDF changed. The introductory coverage summary is reconciled
to the current Section 11 review boundary. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,299 jobs, and the axiom audit passes
13,282 declarations with only the permitted three axioms. The merged source
label audit resolves 3,127 references, and all 1,318 local Markdown
destinations resolve; the 51-report inventory and `git diff --check` pass.

## Omnific root obstructions and residue domains

The Section 12 review compares source 02's quadratic criterion, sources
01–02's initial-form calculation, and source 05's two-term root obstruction
and failed-lifting example. The quadratic argument explicitly includes the
repeated-root case and exhaustiveness. For a nonmonic quadratic it gives the
additional condition `y − b ∈ 2a Oz`; the example `6x² + x − 1`, with square
discriminant `25` but roots `1/3` and `−1/2`, shows why that condition matters.
The initial-form discussion explains the candidate maximum before
cancellation, includes a real-sign obstruction even when two terms have
maximal weight, and handles substitution that makes the polynomial zero.

The two-term root obstruction now has a shorter proof using finite algebra.
For a proposed positive root `x` and the positive monomial root `u`,
`xⁿ − uⁿ = b ≠ 0` factors as `(x − u) S`. Both factors have nonnegative
support, so the constant-product lemma forces `S` to be real; positivity
gives `S ≥ uⁿ⁻¹`, an infinite lower bound. Source 05's binomial expansion is
retained to display the forbidden negative exponent. Its reverse-well-ordered
support and finite convolution fibers are now justified for every positive
surreal exponent, without cofinality or a topological limit.

The failed-lifting example `X² − X − ω` has two simple residue roots, and
its nonsquare discriminant proves absence of an omnific lift using the
finite-algebra obstruction. The notation guide and article distinguish this
constant-term map from the finite-surreal valuation ring's standard-part
map. The polynomial has an infinite coefficient, so it is outside the
hypotheses of the simple-root lifting theorem for that valuation ring.

All 67 standard statements, 159 labels and label numbers are preserved;
main Sections 13–14 are byte-identical. Article and catalogue have clean
three-pass builds of 60 and 28 pages; all 21 changed article pages and four
changed catalogue pages were visually inspected. Source-02 and source-05 SymPy 1.14.0
checks pass, with only source 02's recorded Python version differing from
delivery. Separate finite symbolic checks verify the new discriminant and
factorization examples and the displayed square-root coefficients. Those
checks do not replace the general source proofs. The 51-report inventory
resolves all 2,636 results, and all 3,127 cited source labels and 1,318 local
Markdown destinations resolve. No Lean source or coverage is added; later
sections, imported foundations, source reconciliation and unintegrated
companions remain pending.


## Synchronization of the omnific reviews and expanded collection

The root-obstruction review in `3dd4e2c` is preserved through the assembly
merge `ed7202a` and synchronization with `9693b28`. The Diophantine article
now has 104 standard statements and 228 labels; all statement texts and
labels from the incoming five-source assembly survive. The local root
proof changes survive in Section 15, alongside the incoming pointer to the
sibling report's fresh-scale image-gap theorem. The earlier specialization
review is now Section 14. These numbers replace the historical numbering in
the preceding review records.

The reviewed scope is the **original material in Sections 1–10 and current
Sections 14–15**. New material in Sections 6 and 10, Sections 11–13 and
16–17, and remaining imported results and source reconciliation still need
review. In particular, integration does not certify the newly added
Diophantine definitions or reconstruction arguments.

The reader map, catalogue and ledger now cover 56 main texts and 3,089
standard statements. The quotient assembly, entire-function rectification,
omnific-preserving automorphisms and omnific groups/lattices are recorded
in their current written forms. The three new bases placed in `a4dcb91`
are indexed separately from their four unintegrated companions. Two further
Diophantine fraction manuscripts and three quotient companions also await
integration. The new base READMEs now describe the actual maintained paths,
missing PDFs and scratch-directory verification commands, instead of
claiming that the original delivery layout is still present.

Validation: the merged Diophantine PDF builds in three passes to 88 pages,
and the catalogue to 28, with no warnings or box diagnostics. Rendered
specialization/root pages, section transitions and provenance tables were
inspected, as were all catalogue pages. All 56 catalogue destinations exist.
An independent parser checks the 3,089 ledger rows against their source
statements, labels, headings and line anchors. The source-reference audit
finds no missing labels among 3,582 cited labels; local Markdown links also
pass. All earlier standard statements and labels in the expanded
entire-functions report are retained unchanged. The incoming computer-algebra
correction identifies its `Π ⊕ Z` floor as the omnific floor, consistently
with the shared notation guide.

The corrected commands rerun the three new base finite suites successfully:
41 holonomic-notation groups, 16 Hilbert symbolic checks (including 125
exponent triples), and the HOD suite's finite codes, floor and support-coset
examples. They establish finite regression evidence, not the reports'
transfinite or definability claims. Delivered data files are unchanged.

At synchronization with `9693b28`, the incoming Laurent Cayley implementation
had chart-level coverage; its build passed 4,303 jobs and audited 13,351
declarations. The final fetch brought `934810a`, completing transport to
angular coordinates and identifying the Fourier derivative with the native
fine derivative. Its exact mapping for `trigonometry:thm:stability` is
retained. The combined `LEAN_NUM_THREADS=2 lake build` passes 4,307 jobs and
audits 13,389 declarations, using only `propext`, `Classical.choice` and
`Quot.sound`. All 3,089 statement-index rows, 3,582 cited labels and 1,383
local Markdown destinations pass after that merge. The article and catalogue
PDFs are unchanged by this Lean-only follow-up. This documentation review
adds no Lean coverage of omnific integers.

## Elementary omnific definability: the added Section 11

Reviewed the newly assembled Section 11 against sources 06 and 07 recovered
from `de0acc6`. Its degree algebra, quadratic ideal predicate, Pell rigidity
and divisibility, intersective polynomial, order-free integer definition,
real quintic comparison and natural-number clause are now covered by this
main-text pass. This does not extend the review to Sections 12–13 or to the
inserted material in Sections 6 and 10.

The proof now identifies the unique leading product and explains why a
nonconstant polynomial evaluation has positive degree over an unordered
coefficient field. An intermediate ring need not admit a constant-term
retraction onto its constant subring: `Z[ω + 1/2]` demonstrates the distinction.
The quadratic ideal predicate needs its witness inside the ring;
`Z[ω]` and `Z[√2] + Π` explain, respectively, the witness-closure and
nonsquare hypotheses. The homomorphism argument needs only preservation
of the integer numeral, not of the chosen root or coefficient field.

The Pell recurrence proof supplies an integral inverse matrix and removes
any possible preperiod via a finite pigeonhole argument, including modulus
one. The alternative quotient-ring proof explains its cardinality. The
principal-ideal argument uses algebraicity without assuming integrality.
The intersectivity proof makes CRT assembly explicit and distinguishes
existence of roots at each power of two from lifting a prescribed residue.
The order-free system's witnesses are typed correctly: four are ordinary
integers, while the fifth can be Gaussian. Its proof uses coefficient
intersection, not a retraction. The notation guide corrects the quotient
report's now-obsolete `I` notation and translates its coefficient-restricted
`𝒜_{D,k}` to the Diophantine report's `ℛ_o(k,Γ)`.

All 104 standard statements, all 228 labels and their numbers are preserved.
Section 12 onward is byte-identical in the source. The article builds in
three passes to 89 pages without warnings or box diagnostics; the reviewed
pages, contents and section transitions were visually checked. The catalogue
builds cleanly to 28 pages, and all three changed pages were inspected.
Source 06's finite verification output agrees with delivery except for the
Python version; source 07's output agrees exactly. Neither finite suite
proves the infinite-support or definability claims. The independent inventory
and statement audit passes 3,089 rows in 56 texts, and all 3,582 cited labels
and 1,383 local Markdown destinations resolve. No Lean source changes in
this pass; the 4,307-job build and 13,389-declaration axiom audit from
`c0a36ee` remain applicable. Formalization and the remaining imported-result,
historical-priority and source-reconciliation work stay pending.

The final fetch brought `eeb87b2`, whose sine-square Fourier witnesses prove
sharpness of the angular stability bounds. Merge `e3b086d` retains those
implementation mappings and changes no manuscript or PDF. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,311 jobs, and its axiom audit accepts
13,431 declarations using only `propext`, `Classical.choice` and `Quot.sound`.
The 3,089-row statement audit and 3,582-label audit still pass; all 1,387 local
Markdown destinations resolve.

## Constant-term detector and graph: the added Section 12

Reviewed Section 12 against source 07's augmentation detector, ideal test
and number-field arguments and source 06's retraction and homomorphism
section, using the same `de0acc6` deliveries as the preceding review.
The maintained proof now identifies the full pullback `A = ε⁻¹(o)` and
locates scalar cancellation in the coefficient field. An explicit certificate
in `Z × R` illustrates the allowed zero divisors. A second boundary example,
`Z[ω]` inside `R[ω]`, shows why an ambient root and integer constant terms
do not replace the full pullback hypothesis. General polynomial coefficients
are parameters; the integer coefficients of `Λ` and `Λ_K` are numerals.

The support proof explains finite convolution and retention of the original
exponent group. The ideal's intersection description includes both
directions and its failure over coefficient rings containing `Q`. The graph
proof exhibits its six witnesses and specifies that uniqueness concerns its
output. The quartic degree follows directly from its `x⁴` coefficient.
The canonical splitting has an explicit proof and a multiplication formula
distinguishing the additive direct sum from a ring direct product.
The homomorphism argument separates preservation of existential equations
from automorphism invariance of arbitrary first-order definitions.

The number-field proof now constructs witnesses in the coefficient subring,
without assuming integrality or finite generation. Remark 12.15 adds a
consequence of the combined sources: the detector's assumed root has square
`p`, `q` or `pq`, a nonsquare in the base number field. This radicand gives
a one-witness existential ideal and a six-witness existential graph under
the same hypotheses, alongside the two-witness complement detector. No
additional quadratic extension or uniform formula over all number fields
is asserted. This strengthens the documented conclusion at source level;
all these omnific claims remain **Pending** in Lean.

All 104 standard statement texts, all 228 labels and their numbers remain
unchanged, and Section 13 onward is byte-identical. Three-pass LaTeX builds
produce a 90-page article and 28-page catalogue without warnings or box
diagnostics. The contents, status paragraph, reviewed pages and section
transitions were visually checked, as was the catalogue's sole changed
page. The independent inventory audit checks 3,089 standard results in 56
main texts; 3,585 cited labels and 1,391 local Markdown destinations resolve.
The earlier finite suites are unchanged and were not rerun: they are not
proofs of the added definability consequence.

Before editing, `0502930` was merged by fast-forward. Its conditioned
inverse-cosine Lean results change no manuscript. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,315 jobs, and the axiom audit
accepts 13,458 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The new material in Sections 6 and 10, Sections 13 and
16–17, and remaining imported foundations, historical priority and source
reconciliation still need review.

## Constant-term review synchronized with the fraction integrations

The final fetch brought documentation-only `c060ec8`, including the
fraction integration `b829d8b`, quotient expansion `aae58bb`, and assembled
definable-surreal, notation and Hahn–Hilbert reports (`337d4a4`, `600397e`,
`e118d89`). The merge retains the Section 12 review from `229fe0b`
byte-for-byte and all 143 upstream Diophantine standard statement texts,
310 labels and their numbers. Section 13 onward matches the fetched source.
The added fractions are Section 15; the previously reviewed coefficients
section is now Section 16. Current review boundaries are updated throughout
the reader map, report guide, reconciliation, ledger and catalogue.

The catalogue now describes seven Diophantine and sixteen quotient sources,
and the assembled two-source definability, three-source notation and
two-source Hilbert reports with their maintained PDFs. Their assembly does
not extend proof-review coverage. The ledger now indexes 3,271 standard
results in 56 main texts (1,298 theorems, 668 lemmas, 677 propositions,
628 corollaries), including 143 Diophantine and 227 quotient results. Its
separate nine custom quotient main-theorem anchors are refreshed as well.
The new reports' guides now distinguish these pending index entries from
checked implementation mappings. New archives in `5610500` and `21016dc`
remain to place and reconcile.

The merged Diophantine PDF builds in three passes to 119 pages, and the
catalogue to 28 pages, without warnings or box diagnostics. Widened contents
number columns separate the new `15.10`–`15.12` entries from their titles.
The contents, review status, Section 12 and its transitions were inspected,
as were all eight changed catalogue pages. An independent source inventory
audit passes, all 3,771 cited labels resolve, and all 1,406 local Markdown
destinations resolve. The incoming changes touch no Lean file, root import,
package configuration or toolchain, so the 4,315-job build and
13,458-declaration axiom audit above remain applicable. The full document
review, source reconciliation and formalization goals remain incomplete.

## Final synchronization: the 57th report and Laurent root counts

A further fetch brought `c6359e4` and `b895e86`. The placement adds one
main text on discrete initial subgroups and omnific normalization, plus
eight companions for five existing reports. The reader map and catalogue
now include the 57th report; the ledger indexes its 26 standard statements
and separately records its three custom main theorems. Its guide now uses
the placed file paths and attributes the delivered PDF checks correctly:
no maintained PDF was placed, and no independent proof review is claimed.
The eight new companions remain to integrate.

The ledger merge preserves the completed Section 12 review and the incoming
Laurent algebraization, finite-angle root-count and Fourier-uniqueness
implementation mapping. No already-mapped manuscript changed. The independent
inventory audit passes 3,297 standard rows across 57 main texts; all 3,797
cited labels and 1,413 local Markdown destinations resolve. The expanded
catalogue builds cleanly in three passes to 29 pages; the new entry and
adjacent family transition and final page were inspected. The reviewed
Diophantine source and its 119-page PDF are unchanged in this synchronization.

`LEAN_NUM_THREADS=2 lake build` passes 4,318 jobs. The audit accepts
13,506 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The full review and formalization goals remain incomplete.

## Coefficient reconstruction and logic: the added Section 13

Compared Section 13 with source 06's multiplier, real reconstruction,
automorphism, Gaussian obstruction and logical sections, and with source
07's transfer and omitted-type arguments, using the recovered source versions
identified in the Section 11 record. The review now covers the newly added
Sections 11–13, alongside the previously reviewed original Sections 1–10,
14 and 16. Additions in Sections 6 and 10, Sections 15 and 17–18, the new
companions and remaining foundational/source reconciliation still need review.

The fraction presentation supplies operations, nonzero denominators and
witness domains. The multiplier proof identifies the single translated
coefficient that cannot cancel. Coefficient reconstruction uses units of
the multiplier ring, with zero treated separately, and the corollary now
repeats its standing nontrivial-group hypothesis and includes a proof.
Any parameter-free ideal predicate supports the same reconstruction; in
particular the number-field integer-radicand predicate from Section 12 does
so even when two is a square in the coefficient subring's fraction field.
The standard-part proof uses the largest remaining negative exponent, and
the value-group proof verifies equivalence, ordering and the sign convention
`v = −leading exponent` without adding a definable monomial section.

The automorphism explanations distinguish exponent substitution from
squaring, use finite coefficient convolution without analytic continuity,
and make the composition-preserving coefficient section explicit. The
phase twist fixes every named complex constant; its restriction to the
Gaussian ring fixes all allowable Gaussian parameters. Proper-class
quotients and sentence-by-sentence translations remain distinct from a
global satisfaction predicate.

The c.e.-set proof guards free tuples and transfers its auxiliary witnesses.
Combining it with the order-free integer guard extends the finite-system
classification to every characteristic-zero coefficient field, without
ordering or a square root of two. The same guard proves non-elementarity
when that root is absent. The collapse obstruction specifies strict
positivity, and the singleton `x = h` explains why its coefficient-parameter
restriction matters. The quantifier-free lower bound includes negated
equalities and uses the coefficient predicate to exclude quantifier
elimination without an extra root assumption. Canonical polynomial syntax
makes the omitted type decidable; a sum-of-degrees bound gives an ordinary
integer satisfying each finite part.

All 143 standard statements, 310 labels and their numbers are retained.
Only two standard statement texts change: the explicit standing hypothesis
and strict-positivity wording above. Section 14 onward is byte-identical.
The article builds in three passes to 121 pages and the catalogue to 29,
without warnings or box diagnostics. The reviewed pages, contents, status
and transitions, and the changed catalogue page, were visually checked.
The independent inventory audit passes 3,297 standard rows across 57 texts;
all 3,797 cited labels and 1,419 local Markdown destinations resolve.
The finite suites are unchanged and were not rerun; they would not verify
the logical extensions. These source-level arguments remain **Pending**
in Lean; real closedness, MRDP and historical priority are separate imports.

The initial synchronization fast-forwarded to `0865f04`, including the
angular-multiplicity work `1ced5a4`. It changed no manuscript. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,324 jobs, and the audit accepts
13,560 declarations using only `propext`, `Classical.choice` and
`Quot.sound`.

The final fetch added `cf56b89` (sine-family sharpness and finite-angle
root classes), merged in `a094091`. It changes no manuscript or PDF.
The combined two-thread build passes 4,326 jobs and audits 13,608
declarations with the same three permitted axioms. All 3,797 cited labels
and 1,421 local Markdown destinations resolve; the 3,297-row source
inventory is unchanged.

## Omnific denominator ideals and multipliers: Sections 15.1–15.4

The [Diophantine article](surreal/omnific-diophantine-geometry/article.tex)
now has an independent proof review through the affine denominator
dichotomy. Its [reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md)
identifies the recovered source-08 and source-09 archives and exact
sections compared. Sections 15.5–15.12, the new material in Sections 6
and 10, Sections 17–18, new companions and remaining imported foundations
and source reconciliation remain outside this completed review.

The calculus proof spells out translation, reciprocal and projective
covariance identities, including why the scaled ideal is still omnific.
Translation now includes zero. A finite tuple has a nonzero common
denominator; the analogous assertion over an arbitrary domain requires
membership in its fraction field. Least denominators use ordered division
once per element and cancellation, without a Euclidean-termination claim.
The ordinary localization proof gives its additive splitting and units,
restores the finite-factorization proof for algebraic surreals, and provides
explicit witnesses for the strict ring inclusions. Real-constant arguments
cover zero, divisibility by every ordinary integer and the no-gcd step.

The multiplier proof tracks the inverse rescaling of its Bézout row and
the original scalar lattice `λR_ℤ` before normalization. It permits a zero
retraction kernel. The pair `(ω,ω)` illustrates why ambient unimodularity
is necessary. The alternative lift now specifies its ordered-pair syzygy
sum and verifies both its zero pairing and its residue. Polynomial
indeterminates, evaluated parameters and determinant notation are aligned
with the shared guide. Remark 15.16 corrects the source's scope: the
denominator equivalences apply to affine points, while infinity only has
the projective specialization and unimodular-presentation assertions.

All 143 standard statements and 310 labels are preserved, with unchanged
numbering. Only the calculus proposition changes standard-statement
wording, restoring translation at zero. Section 15.5 onward is
byte-identical. Three-pass pdfLaTeX builds produce a clean 122-page article
and 29-page catalogue, without warning, reference or box diagnostics.
Visual inspection covers article PDF pages 5, 11 and 68–76 and all four
changed catalogue pages, 9–12. The independent inventory verifies 3,297
standard results across 57 main texts; all 3,797 cited source labels and
1,426 local Markdown destinations resolve. The delivered finite verifiers
are unchanged and were not rerun: they do not establish these general
ideal and multiplier arguments. The source-level results remain **Pending**
in Lean.

The initial synchronization fast-forwarded to `ba6dff6`, adding the
stationary-angle work without changing any manuscript. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,329 jobs and audits 13,627
declarations, using only `propext`, `Classical.choice` and `Quot.sound`.

The final synchronization merged `bf428a5` in `17aa289`, adding two
polynomial-positivity modules and no manuscript changes. The combined
build passes 4,331 jobs and audits 13,640 declarations with the same
three permitted axioms. The source-label and independent inventory audits
still pass; both reviewed PDFs remain identical to the validated builds.

## Omnific rational functions, curves and focusing: Sections 15.5–15.7

The [Diophantine article](surreal/omnific-diophantine-geometry/article.tex)
now has a proof review through the congruence-orbit and dense-fiber
arguments. The [reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md)
records comparison with source 08's Sections 6–7 and source 09's Sections
7–9, using the archived texts recovered in the preceding pass. The
elementary-group comparison was checked against the cited cusp-residue
statement and matrices in the groups report; its amalgam theorem and
full proof remain separate imported dependencies.

The polynomial evaluation proof now includes fraction-field injectivity
and the leading-degree formula for rational functions. The classification
tracks normalization of the denominator and uniqueness of the nonzero
multiplier, and verifies independence of projective specialization from
the chosen reduced vector. Lowest terms, the zero function and formal
poles are explicit. The worked table has coprimality checks, and the
certificate procedure spells out finite coordinate-ratio tests and the
parameter-dependent sign needed for a positive denominator.

The local-density construction specifies positive integer exponents,
vanishing orders and a strict degree bound. Its topology comparison now
has a concrete proof: a single exponent larger than every ordinary
multiple of `deg_ω(t)` gives a positive radius isolating every element
of the fixed field `R(t)` in the induced surreal topology. The degree
topology remains non-discrete. The no-lcm argument identifies both
ideal inclusions, and the homogeneous-system proof uses homogeneity to
justify the real normalization and shows why a nonconstant coordinate
is infinite in absolute value.

The orbit theorem now says real projective point, including infinity.
The topology is defined in both affine charts, and nowhere continuity
uses relative neighborhoods at infinity as well. The focusing lemma
previously used `1/b` at the allowed value `b = 0`; the statement now
gives the identity at zero, restricts that formula to nonzero `b`, and
identifies the pole `x − 1/b`. The focusing bound excludes that pole
from the prescribed set. A single matrix supplies both nearby
denominator types, with the transformed column and its residue explicit.

All 143 standard results and 310 labels are preserved, with unchanged
numbering. Four standard statement texts change: the orbit theorem,
focusing lemma, dense-fiber corollary and nowhere-continuity corollary.
Section 15.8 onward is byte-identical. Three-pass pdfLaTeX builds give
a clean 123-page article and 29-page catalogue, with no warnings,
unresolved references or box diagnostics. Visual inspection covers
article PDF pages 5, 6, 11, 68 and 75–83 and the changed catalogue page 9.
The independent inventory verifies 3,297 standard results in 57 main
texts; source-label and local Markdown link checks pass.

The delivered finite verifiers were rerun with SymPy 1.14.0 in scratch:
source 08 passes 833 assertions and exactly reproduces its recorded JSON;
source 09 passes 92, differing only in timestamp and Python version.
Their symbolic identities and finite examples do not verify the
proper-class focusing, topology or denominator classification proofs.
No delivered script or recorded JSON was overwritten. No Lean source is
changed by this review, and all these results remain **Pending** in Lean.

The initial fetch found the branch synchronized at `9e95be1`. The
remaining review starts at Section 15.8; later fraction material,
Sections 17–18, added material in Sections 6 and 10, new companions,
imported foundations and source reconciliation remain outstanding.

The final synchronization merged `64571c3` and `bcac55a` through `129a053`,
adding nonnegative-polynomial norm factorization and affine Cayley-chart
Fejér–Riesz construction. No manuscript changed. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,340 jobs and audits 13,715
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
All 3,799 cited source labels resolve and the 3,297-row inventory still
passes; both reviewed PDFs match their validated builds byte for byte.
The local Markdown check resolves 1,430 destinations in 153 files.

## Omnific localization, scale defects and Gaussian fractions: Sections 15.8–15.12

The [Diophantine article](surreal/omnific-diophantine-geometry/article.tex)
now has a manuscript proof review throughout Section 15. The
[reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md)
records comparison with source 08's Sections 8–13 and source 09's
monomial, workspace and Gaussian discussion, using the archived texts
recovered in the preceding passes. The sibling report's finite-support
core and unit-forcing localization statements were checked for the
comparisons made here; their full proofs remain imported dependencies.
The equational flatness criterion and Tor exact-sequence facts were
checked against the primary Stacks Project sources, [Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
and [Section 10.75](https://stacks.math.columbia.edu/tag/00LY), on
23 September 2026. The existing bibliography entry now includes both.

The previous claim that standard part and rational residue agree only
on `ℚ` was false. For positive `t ∈ Π`, the nonzero infinitesimal
`t/(t+1)²` has both residues zero. The revised text proves the exact
agreement locus `ℚ ⊕ (ker st ∩ ker res)` additively. It also uses a
positive element with negative rational residue to establish failure
of weak order preservation. The localization proof identifies the
nonunits, unique maximal ideal and fraction field. Quotient language
uses ordinary residue pairs as representatives, avoiding set-valued
proper-class cosets.

Polynomial division proves the one-parameter intersection, and the
generator count uses cardinalities of finite integer linear combinations.
The scale-defect proof gives the module map, its truncated representatives
and its real coefficient dimension. A proved combined consequence
distinguishes that finite dimension from infinite module length: the
top layer contains `ℤ ⊊ (1/2)ℤ ⊊ (1/4)ℤ ⊊ …` as submodules.
The integrality and non-finiteness arguments are expanded. Nonflatness
computes both relation modules, and the Tor proof identifies the new
relations modulo the image of the old ones through right exactness.
It does not assume that the tensor of the original kernel injects.

The fixed-workspace example now proves both localization inclusions
and gives the coefficient recurrences excluding the two nonrational
series. Gaussian evaluation, normalization, Bézout transport, non-set
generation and the no-gcd argument are explicit. The constant-direction
proof permutes a nonzero coordinate into the denominator position before
using the affine theorem. The complex standard part and Gaussian-rational
residue have consistent names and coordinatewise finiteness domains.
Shared notation and the collection guides reflect these distinctions;
the root README highlights the manuscript results separately from Lean
coverage and uses the two-thread build command.

All 143 standard statement texts, 310 labels and result numbers are
unchanged. Section 16 onward is byte-identical except for the expanded
Stacks bibliography entry. Three-pass pdfLaTeX builds give a clean
125-page article and 29-page catalogue, without warnings, unresolved
references or box diagnostics. Visual inspection covers article PDF
pages 5, 11, 68, 83–91 and 125, and catalogue page 9. The independent
inventory verifies 3,297 standard results in 57 main texts, and all
3,800 cited source labels resolve. Local Markdown link checks pass.

The source-08 and source-09 finite verifiers pass 833 and 92 assertions
under SymPy 1.14.0. The first reproduces its recorded JSON exactly; the
second differs only in timestamp and Python version. Neither verifies
the class-sized arguments or full Tor theorem. Delivered scripts and
recorded verification data are unchanged. These manuscript results,
including the two explicit combined consequences, remain **Pending**
in Lean.

The branch was synchronized through `0fffc26` and fetched again at the
user's request, then fast-forwarded to `d8ce588`. No incoming manuscript
changed. The combined `LEAN_NUM_THREADS=2 lake build` passes all 4,346
jobs; its audit accepts 13,755 declarations with only `propext`,
`Classical.choice` and `Quot.sound`. This validates the merged Lean
library; it does not formalize the manuscript revisions. Sections 17–18,
added material in Sections 6 and 10, companions, imported foundations
and remaining source reconciliation still require review.

## Combined validation after the batch-28 and new-manuscript merge

The fraction review was committed as `b2a8686`. A pre-push fetch found
eleven incoming commits through `6f47cf9`; merging them preserves the
reviewed Section 15 and incorporates the new curve/differential material
in Sections 16–18. The old Sections 16–18 are now 19–21. The combined
article has 194 standard statements and 405 labels; all 143 preceding
statement texts and all 310 preceding labels survive. Result numbers
through Section 15 are unchanged, and the body of that section from its
conventions subsection to the next section is byte-identical to `b2a8686`.
The new curve material, its pointers and additions remain outside the
completed proof review. Earlier review records use their then-current
section numbers and counts.

Three-pass pdfLaTeX builds produce a clean 163-page article and 29-page
catalogue. The source-label and independent inventory audits pass after
updating renamed normalization labels and indexing the current assemblies:
3,428 standard statements in 58 main texts, with 3,934 cited labels
resolved. Existing statement texts referenced by the Lean implementation
table do not change in this incoming merge. All incoming files are under
`docs/`, so the successful 4,346-job Lean build and 13,755-declaration
audit at `d8ce588` remain the relevant build validation; no additional
Lean build is needed for this merge.

The inventory and reader map now include the newly placed quantum/gauge
base. Its local guide distinguishes the actual repository paths from
the delivered package's filenames. The catalogue and root README reflect
the current assemblies and preserve their pending review status. The
companions placed in `66d7e55` and the nine archives in `190d301` still
need integration or placement and reconciliation; indexing the main
texts does not establish coverage of those separate manuscripts.

## Combined validation with Fejér–Riesz uniqueness and coefficient bounds

After the documentation merge `e8dcd56`, the next fetch found four commits
through `cfd1c89`. Their README and coverage-inventory refresh were
reconciled with the manuscript review, preserving the updated 58-report
inventory and the distinction between written and Lean-checked results.
No manuscript source changed in this merge, so the clean combined PDFs
remain current. The source-label, independent inventory and Markdown
link audits pass: 3,934 cited labels, 3,428 indexed statements and 58
main texts. `LEAN_NUM_THREADS=2 lake build` passes all 4,353 jobs, and
the audit accepts 13,813 declarations with only `propext`,
`Classical.choice` and `Quot.sound`. The incoming formalization completes
normalized Fejér–Riesz uniqueness and adds actual-field Fourier coefficient
bounds. It does not change the pending Lean status of the omnific results.

## Gaussian fibers and étale norm proof review

The additions from sources 07 and 13 to Section 6 of the omnific
Diophantine report have now been compared with the delivered sources.
The Gaussian fiber proof constructs its parameters coefficientwise on a
common admissible support and proves uniqueness. The real kernel test
uses the stacked real and imaginary parts of the matrix. An explicit
empty-fiber example explains the ordinary-point hypothesis; when that
hypothesis holds, a nonzero kernel vector gives a proper class of points.

The étale norm proof now explains separable splitting, the invertible
matrix of algebra maps, the bilinear trace matrix, and coefficient
extension. It uses the constant intersection of the intermediate ring
only after showing that each coordinate is constant. Boundary examples
show why a nonzero level and the étale assumption matter. The abstract
Hahn-ring argument extends to arbitrary characteristic; a purely
inseparable quadratic example in characteristic two shows why separable
splitting is still needed. This extension does not change the coefficient
fields of the actual omnific rings. Shared notation also corrects the
detector name to match the maintained `Ex` macro.

All 194 standard statement texts, 405 labels and existing result numbers
are unchanged. Section 7 onward is unchanged except for the appended
Stacks bibliography entry. Three-pass pdfLaTeX builds give a clean
164-page article and 29-page catalogue. Rendered article pages 12,
28–35 and 164, and catalogue page 9, have been inspected. The independent
inventory verifies 3,428 results in 58 main texts; all 3,934 cited source
labels resolve, and local Markdown links pass. Both supplied finite
verifiers (07 and 13) reproduce their recorded outputs exactly; these
checks do not prove the general Hahn-series arguments.

The new combined consequences and characteristic extension remain
**Pending** in Lean. Source 07's quartic in Section 10, the curve
material and pointers, companions, imported foundations and remaining
source reconciliation still require review.

## Combined validation with batch 29 and the actual omnific ring

The Gaussian-fiber and norm review was committed in `85887ed`. Merging
the twenty incoming commits through `751ff27` preserves that work and
incorporates six expanded manuscripts: logarithmic rigidity, exact
homological dimensions, elementary-group kernels, convex factors and
profinite obstructions, compact groups, and quantum/gauge reductions.
These additions are indexed, but their independent proof review remains
pending. The reader map and catalogue now describe the written assemblies
and link the maintained quantum/gauge PDF.

The combined Diophantine article preserves all 200 incoming standard
statement texts and 416 labels, with no changes to existing result
numbers. Clean three-pass builds give a 175-page article and 29-page
catalogue. The independent inventory verifies 3,592 statements in 58 main
texts. Mapped statements in the changed manuscripts retain their text;
the ring proposition and its new actual-field implementation were compared
directly. The formalization route and repository comparisons now replace
stale claims that no omnific Lean code exists with the exact ring and
constant-term coverage supplied by `f879c1e`. Historical source claims
remain identified by their pins.

The source-label audit resolves all 4,126 references, and all 1,501 local
Markdown destinations pass. Visual inspection covers combined article
pages 16, 35, 125–126, 146–148 and 175 and catalogue pages 2, 8–10,
25–26. The article and catalogue logs have no warnings, unresolved
references or box diagnostics.

`LEAN_NUM_THREADS=2 lake build` passes all 4,380 jobs; the audit accepts
14,672 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. This validates the merged library, including the incoming
omnific construction, and does not establish the pending manuscript proofs.

## Placement reconciliation after the second synchronization

The next fetch brought three documentation commits through `0e4dc98`,
merged as `516bb70`. Placement `21375f8` retires the nine archives from
`190d301` into two report bases and companions to three existing reports.
No existing manuscript body or Lean source changed in this merge. The
4,380-job build and 14,672-declaration audit therefore remain applicable.

The inventory now includes the autonomous-dilation base and the
critical-point-defects base: 3,650 standard statements in 60 main texts.
The independent index audit passes, all 4,183 cited labels resolve, and
all 1,517 local Markdown destinations pass. Their local guides explain the
installed paths separately from delivered filenames; their proof reviews,
formalization and remaining companion assembly are pending. The reader
map, root README and catalogue reflect this placement. The catalogue has
a clean three-pass 29-page build, with its first page and the new entries
on pages 25 and 29 inspected. No new manuscript theorem is claimed proved
by these navigation and build checks.

## Catalogue synchronization before publication

The first push was rejected after `main` advanced to `b5f0bfd`, a
documentation-only catalogue and README revision. The merge retains its
expanded report descriptions and root overview, the 60-report inventory,
and the precise Section 6 review boundary and characteristic distinction.
The Diophantine article and Lean files do not change. The combined
catalogue compiles cleanly in three passes to 32 pages; its revised
Diophantine entry and final entry were inspected on pages 9 and 32.
The independent 3,650-statement inventory, 4,183 source references and
1,520 local Markdown destinations pass. The earlier two-thread Lean build
remains applicable.

## Omnific quartic and elementary Euler prerequisites

The remaining source-07 quartic in Section 10 now has a full argument for
arbitrary intermediate rings with integer constant intersection. The proof
separates ambient Pell factorization from membership in the intermediate
ring, proves that every witness is ordinary, and constructs witnesses
from an unbounded ordinary Pell sequence and four squares. The comparison
with the delivered Section 8 is recorded in the Diophantine reconciliation.

The elementary ring and Euler subsections 16.2–16.3 were reviewed next.
The proof now identifies the opposite ring's fraction field, units,
maximal ideal and residue field. It corrects the zero-exponent-group
exception to the non-valuation-ring claim and the false suggestion that
an Euler image inclusion must be proper. Explicit examples establish
both corrections. The logarithmic-derivative residue is now computed
as `ct(∂_λ u/u) = λ(deg u)`, and polynomial Bézout makes the joint-constant
argument for relative algebraic closedness explicit. The shared notation
and review boundaries reflect these distinctions. The squarefree
certificate and geometric arguments remain outside this pass.

All 200 standard statement texts, 416 labels and existing result numbers
are preserved. The source-07 verifier reproduces its recorded output
exactly, without establishing the general Hahn-series claims. The new
residue identity and the reviewed elementary results remain **Pending**
in Lean. No Lean file changes in this review.

Clean three-pass pdfLaTeX builds produce a 176-page article and 32-page
catalogue, without warnings, unresolved references or box diagnostics.
Rendered article pages 13, 48–49 and 96–99 and catalogue page 9 have
been inspected. The independent inventory validates 3,650 statements in
60 main texts, all 4,184 cited source labels resolve, and all 1,520 local
Markdown destinations pass. The previous 4,380-job Lean build and
14,672-declaration axiom audit remain applicable to the unchanged library.

## Combined validation with omnific units and floor

After committing the quartic/Euler review as `6a2d12d`, synchronization
through `de84022` adds actual omnific degree laws, unit and finite-element
classifications, discrete ordering and the exact omnific floor. The source
statements were compared with their new mappings; the manuscript bodies
are unchanged by those incoming commits. Coverage notes now include
these proved results while retaining the pending quartic and geometric
claims. Clean three-pass builds retain the 176-page article and 32-page
catalogue. The 3,650-statement inventory, 4,185 source references and
1,527 local Markdown destinations pass.

`LEAN_NUM_THREADS=2 lake build` passes 4,386 jobs, and the axiom audit
accepts 14,739 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. This build verifies the merged library, not the remaining
manuscript proofs.

## Combined validation with ordinary polynomial-root rigidity

The following incoming commit `e69defb` proves ordinary polynomial-root
rigidity in the real and complex support rings and the omnific ring,
including transcendence over the ordinary reals of every infinite omnific
integer. Its statements agree with the unchanged proposition in the report.
The coverage notes now include this result. All 200 standard statement
texts, 416 labels and existing result numbers remain unchanged from the
start of the review. Clean three-pass PDFs retain 176 and 32 pages; the
final formalization page was inspected on article page 127.

The 3,650-statement inventory, 4,185 source references and 1,530 local
Markdown destinations pass. The final `LEAN_NUM_THREADS=2 lake build`
passes 4,388 jobs; its axiom audit accepts 14,747 declarations with only
`propext`, `Classical.choice` and `Quot.sound`. The quartic and generic
Euler proof review remains manuscript work; their unmapped results still
await Lean proofs.

## Omnific squarefree and Weierstrass proof review

The maintained Section 16.4 now has a proof review through singular
cubic families. The positive-support degree argument handles the
quadratic endpoint without assuming a divisible or nonzero exponent
group. Differential division now explicitly requires an ordinary
integer `m ≥ 1`. The cubic certificate distinguishes the identity valid
at all discriminants from the normalization requiring `Δ₀ ≠ 0`, and
its proof establishes squarefreeness in both directions.

A factor-of-two error in the contraction comparison is corrected:
the assembled squarefree proof uses the contraction of `dx/y`, whereas
the direct cubic proof uses that of `dx/(2y)`. The targeted comparison
with source C13 confirms that its own normalization was consistent.
The rewritten proof explains regularity on two covering affine opens,
the projective coordinate change for general Weierstrass models, and
the zero-parameter case of the singular family. General geometric
foundations remain imported; the two-ring principle and later
geometric proofs remain outside this review.

Exactly three of 200 standard statement texts change: differential
division, the cubic proposition and the short Weierstrass corollary,
whose integer and Gaussian specializations now repeat the discriminant
hypothesis explicitly; all 416 labels and existing
result numbers are preserved. C13 and C14's finite verifiers pass
12,874 and 3,440 assertions and reproduce their recorded results apart
from the Python version. These checks do not establish arbitrary Hahn
support or geometric claims. The reviewed squarefree and Weierstrass
results remain **Pending** in Lean.

Synchronization through `40a3990` adds the actual omnific ordinary
residue rings and integer-divisor rigidity. Their source statements
were checked against the new mappings; the report and catalogue now
include that coverage. `LEAN_NUM_THREADS=2 lake build` passes 4,393
jobs and audits 14,779 declarations with only `propext`, `Classical.choice`
and `Quot.sound`.

Clean three-pass builds produce a 177-page article and 32-page catalogue,
with no warnings, unresolved references or box diagnostics. Article
pages 99–102 and 128 and catalogue page 9 were visually inspected.
The independent inventory validates 3,650 standard results in 60 reports;
all 4,188 cited source references and 1,535 local Markdown destinations
resolve. The root README and exact review boundaries are refreshed.

## Combined validation with ordinary arithmetic and finite quotients

After the squarefree review commit `fbe795f`, synchronization through
`753f4b5` adds `odg:cor:mixedgcd` and `odg:cor:charideals`: ordinary
primes and maximal ideals, mixed gcds, finite Chinese remainders, unique
ordinary moduli for proper ideals containing an integer, and factorization
of every finite-target homomorphism through the constant term. The
incoming declarations and mappings agree with the unchanged manuscript
statements. The report guide includes this new coverage; the later
geometric results remain pending. No LaTeX or PDF changed in this sync.

The combined `LEAN_NUM_THREADS=2 lake build` passes 4,406 jobs and its
axiom audit accepts 14,809 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. All 4,188 cited source references
and 1,539 local Markdown destinations resolve. The squarefree proof
review remains distinct from this new checked ordinary arithmetic.

## Two-ring differential principle and tangent detection

The next Diophantine pass reviews the remainder of Section 16, from
differential separation data through inheritance. The scalar conventions
now distinguish a field derivation over `k` from its tangent functional
after base change to `L`. The two contractions agree by naturality of
Kähler differentials even without a map between the rings or a common
affine chart. The valuation-ring contraction lies in the `r`th power
of its maximal ideal. The symmetric clause explicitly requires positive
degree; the constant section `1` explains the excluded endpoint.
Symmetric evaluation is defined on the quotient symmetric power and
does not rely on lifting global sections to tensor sections.

The proper-rigidity proof now uses right exactness of pullback at the
field-valued point. It also proves the consequence without smoothness,
assuming global generation of the Kähler differential sheaf. Symmetric
rigidity extends to arbitrary separating data. For smooth projective
schemes, a finite-cover and common-degree argument proves that tangent
detection is equivalent to semiampleness of the tautological quotient
line bundle. This is not asserted necessary for rigidity itself.
Inheritance now spells out the fiber-product argument and the absence
of smoothness restrictions on the immersed subscheme.

Explicit examples explain why finitely generated coordinate algebras
need not be stable under Euler differentiation and why a rational form
with a pole cannot replace a global regular form. The zero exponent
group, positive tensor degree and complex finite-element conventions
are explicit. The introduction now distinguishes C11/C13's arbitrary
characteristic-zero proper-rigidity statements from their more restricted
curve classifications. The targeted source comparison and imported
Stacks hypotheses are recorded in the report's reconciliation file.
The root README, notation guide and catalogue reflect this review.

One of 200 standard statements changes, the annihilation theorem's
positive-degree clarification. The other 199 statements, all 416 labels
and existing result numbers are unchanged. All Section 16 results and
the new prose consequences remain **Pending** in Lean. The curve
classification, subsequent applications, earlier pointers and remaining
source reconciliation still require review. No finite symbolic check
is offered as verification of the geometric argument.

Clean three-pass builds give a 178-page article and 32-page catalogue,
without warnings, unresolved references or box diagnostics. Rendered
article pages 102–106 and catalogue page 9 were inspected. The
independent inventory validates 3,650 standard results in 60 reports;
all 4,188 source references and 1,539 local Markdown destinations resolve.
The library is unchanged by this pass; the preceding 4,406-job build and
14,809-declaration axiom audit remain applicable before synchronization.

## Combined validation with canonical constant extraction

After the two-ring review `bf1d084`, synchronization through `5da5961`
adds canonical constant extraction, endomorphism preservation, a concrete
noninjective constant endomorphism and non-residual-finiteness of the actual
omnific ring. The new declarations agree with the unchanged source
proposition and its following example; the latter finiteness result does
not claim the pending inverse-limit or topology constructions. The
report guide now includes this coverage. Two incoming index entries
were corrected: the logit and Christoffel labels belong to equations
inside unlabeled results, not to the enclosing result environments.

The combined `LEAN_NUM_THREADS=2 lake build` passes 4,407 jobs and
audits 14,830 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The independent inventory still validates 3,650 standard
results, of which 19 are unlabeled, across 60 reports. All 4,189 source
references and 1,542 local Markdown destinations resolve. No LaTeX or
PDF changed in this synchronization; the clean 178/32-page artifacts
remain current.

## Combined validation with the ordinary p-adic completion

The next sync through `6a30999` proves the p-adic clause of
`odg:eq:profinite` using Mathlib's actual ideal-adic completion and
p-adic integers. The transition maps, both inverse ring maps, the
constant-term formula for the canonical map and its purely infinite
kernel are explicit. The source equation agrees with that scope; the
profinite completion and congruence-topology assertions remain pending.
The report guide and incoming root README distinguish those obligations.

The final `LEAN_NUM_THREADS=2 lake build` passes 4,413 jobs and audits
14,859 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. The independent 3,650-result inventory, all 4,189 source
references and 1,544 local Markdown destinations pass. LaTeX and PDFs
are unchanged by this sync, so the 178/32-page build and visual checks
remain applicable. Section 17 and subsequent manuscript work remain
outside the completed review.

## Smooth-curve classification and geometric boundary review

The Diophantine review now covers Sections 17.1–17.2, from the canonical
bundle lemma through the classification of all smooth curves. The proof
supplies closed-point evaluation and Nakayama, explains ambient-field
contractions without derivation-stable function fields, and makes the
finite geometric boundary explicit. Descent of an affine-line isomorphism
across any field extension uses genus and the degree of the finite étale
boundary; no embedding of that extension into an algebraic closure is needed.

The real unit circle has two conjugate boundary points and belongs to the
two-puncture case after complexification. The assembly had misleadingly
attached this example to the one-boundary-point affine-line-form argument.
C13's original paragraph referred to its full real-descent proof. The
hyperbola paragraph now distinguishes its constant coefficient-field points
from its two real omnific-integer points. In the logarithmic proof the
valuation centre is closed and lies on the boundary, the local parameter
has nonzero image in the maximal ideal, and both contractions refer to
the same rational differential. The local expression, affine-line pole
order and nonnormal cusp example are spelled out.

The targeted comparisons with C12, C13 and C14, including archive members,
are recorded in the report's reconciliation file. The Stacks curve
compactification, affineness and genus-zero results were checked for the
needed hypotheses and cited. This is manuscript proof review, not new
Lean coverage. Sections 17.1–17.2 remain **Pending** in Lean; arithmetic
fibers, subsequent geometric applications and full source reconciliation
remain outside this pass.

The article retains 200 standard results and all 416 labels and their
existing numbers. Only two standard statement texts change:
`odg:cr:lem:punctures` specifies a finite set of closed points, and
`odg:cr:lem:logdim` specifies integrality and a closed point for the local
parameter. The other 198 standard statements are unchanged. Three-pass
article and catalogue builds produce 178 and 32 pages with no warnings,
unresolved references or bad boxes. Article PDF pages 106–110 and catalogue
page 9 were inspected visually. The independent index audit checks
3,650 results in 60 reports; the source audit resolves 4,189 references,
and the Markdown audit finds no broken local destinations. No finite
verifier is claimed to validate these geometric arguments. No Lean source
changed in this review.

## Synchronization after the smooth-curve review

The merge through `1ab41af` brings in the first four batch-30 report writes
and `2f32ce4`'s Lean congruence topologies. The latter defines the ordinary
congruence topology from positive-modulus ideals and the prime-adic topology
using Mathlib's ideal-adic construction. For both, the closure of zero is
the purely infinite ideal, indistinguishability means equality of constant
terms, and the actual separation quotient is ring-isomorphic to `ℤ`.
The source paragraph following `odg:eq:profinite` and the incoming mappings
were checked. Completion homeomorphisms, topological identifications with
integers carrying arithmetic topologies, and the profinite inverse limit
remain **Pending**.

The combined `LEAN_NUM_THREADS=2 lake build` passes 4,416 jobs and the
axiom audit covers 14,910 declarations using only `propext`,
`Classical.choice` and `Quot.sound`. No other Lean build was active when
this validation began. This build validates the merged library; it does
not formalize the reviewed curve arguments.

The four report expansions retain all previously mapped theorem and
equation texts in those reports. Their new material remains unreviewed
and pending in Lean. The current index is refreshed to 3,730 results in
60 reports, with 3,711 labeled and 19 unlabeled entries; 109 use typed
labels. The renamed autonomous-dilation labels now use `adr:`. All 4,269
cited source references resolve. The nine archives placed in `39fe674`
are incoming material, not reviewed or indexed maintained articles.

## Arithmetic-fiber and polynomial-witness review

The Diophantine review now covers Section 17.3, Theorems 17.11–17.17 and
the intervening example. Closed affine presentations are explicit, and
equations descend through the injective arithmetic-to-support-ring map.
The example `2Y=0` demonstrates that the integral model need not be flat.
The proof treats the zero exponent group separately and corrects a scope
ambiguity: fixed-workspace fibers are sets, whereas the proper-class
conclusion uses all surreal supports.

The integer-arc proof expands denominator clearing and cancellation.
Clearing the inverse identity extends injectivity to any torsion-free
`ℤ`-algebra; `q(S)=2S` on `ℤ × 𝔽₂` explains why characteristic zero alone
does not suffice. The congruence criterion supplies its inverse, the
modulus-one case, and the empty-or-countably-infinite consequence for the
ordinary point set with a supplied parametrization. Multiplication by the
clearing integer is bijective on `Π`, so the integer polynomial arc still
parametrizes the entire exceptional fiber. In particular, a nonordinary
point has a finite-support witness in the same fiber with coordinates in
`ℤ[ω^γ]` for one positive exponent.

The polynomial-witness proof translates the parameter explicitly. The
separated-model proof distinguishes a point from its constant extension
and gives the closed-equalizer ideal argument. The report reconciliation
records targeted comparisons with C11–C14 and the checked separatedness
reference. These results and the added prose consequences remain
**Pending** in Lean. Projective coordinates, later geometric applications
and full source reconciliation remain to be reviewed.

Validation: three-pass article and catalogue builds give 179 and 32 pages
with no warnings, unresolved references or bad boxes. Article PDF pages
110–114 and catalogue pages 9–10 were inspected visually. All 200 standard
results, 416 labels and existing result numbers are preserved. Exactly
three statement texts now specify closed affine presentations:
`odg:cr:thm:arith`, `odg:cr:cor:omnific` and `odg:cr:lem:arcs`; the other
197 are unchanged. SymPy 1.14.0 verifies the two displayed integer arcs,
the admissible residues modulo three and the shifted-parabola identity;
these finite checks do not verify the geometric proofs. The independent
inventory audit checks 3,730 results in 60 reports, all 4,269 cited source
references resolve, and the local Markdown link audit passes. No Lean
source changed in this review.

The catalogue also corrects a stale description of the incoming
omnific-preserving-automorphism assembly: it now contains eight manuscripts
and states automatic strongness for `Oz` automorphisms in Part III. The
catalogue previously still described this as open in the written text.
The updated synopsis was checked against `opa:as:thm:main` and
`opa:as:thm:explicit`; it reports their claims as awaiting proof review and
Lean formalization, preserving the unresolved Gaussian compatibility case.

## Profinite completion and independent-copies placement

The merge through `4253328` brings in `5edd752`'s profinite completion and
`9d28e28`'s new report placement. The profinite construction uses the actual
positive-modulus diagram, reduction maps, compatible-section ring and a
proved limit universal property in `CommRingCat`. Its componentwise
constant-term isomorphisms respect reduction, identify the canonical map,
and give exactly the purely infinite ideal as kernel. Every finite-index
omnific ideal occurs, including the unit ideal at modulus one. The source
paragraph at `odg:eq:profinite` and the incoming mapping were read; topology
on the limit carriers and completion homeomorphisms remain **Pending**.

The combined `LEAN_NUM_THREADS=2 lake build` passes 4,418 jobs and audits
15,013 declarations using only `propext`, `Classical.choice` and `Quot.sound`.
No other Lean process was active when it began. The incoming placement
changes none of the previously mapped manuscript statements.

The independent-copies base is now included in the report navigation,
catalogue and ledger: 29 standard environments, plus its three separately
styled main theorems as additional obligations. Its claims and NBG with
Global Choice foundations remain unreviewed and pending in Lean. Its
README now uses the actual repository filenames; a three-pass build
produces the missing 25-page PDF without warnings. The catalogue also
builds in three passes without warnings and remains 32 pages. Its dilation
entry now links the written PDF and retains the report's single-source
provenance. The other
eight placed manuscripts are companions awaiting integration; their
delivered verification files are not treated as checked proofs.

The independent inventory audit passes for 3,759 standard results in
61 reports, including 3,740 labeled and 19 unlabeled entries. All 4,301
cited source references resolve, local Markdown destinations pass, and
`git diff --check` is clean. The arithmetic-review article is unchanged
by this merge and remains 179 pages. This synchronization adds no Lean
coverage for the reviewed geometric arguments.

## Projective-coordinate proof review

The Diophantine review now covers Section 17.4: the unimodular theorem,
invertible-quotient construction, coordinate-ideal classification, rational
projective corollary, elliptic example and field-point remark. The proofs
distinguish invertibility from generating the unit ideal, identify the
generic quotient coordinates, and explain the scalar step that recovers
the original unimodular tuple. The full-class ideal theorem now exhibits
finite inverse-ideal witnesses and includes their numerators, denominators
and products in one workspace. The Gaussian case includes its four units.

The cross-section claim that both the rational-curve and rigid-target
results make a principal coordinate ideal imply a rational point was false.
The counterexample `[ω:1]` has coordinate ideal `Oz` and rational
constant-term specialization `[0:1]`, but is not a `ℚ`-point. The revised
comparison keeps rational specialization distinct from rationality of the
point itself and retains the rigid-target hypothesis. The notation guide
also distinguishes this constant-term specialization from projective
standard part `[1:0]`.

The elliptic example now checks smoothness at infinity and gives the
support inequalities behind its clearing monomial and common nonunit
divisor. The field-point remark distinguishes square-root existence from
the negative-tail obstruction and explains Hahn summability. Targeted C12
and C14 comparisons and the projective-space reference are recorded in
the report reconciliation. No theorem statement changes and no new Lean
coverage is claimed. Section 17.5, later applications and full source
reconciliation remain pending review.

The three-pass article/catalogue builds produce 180/32 pages without
warnings, unresolved references or bad boxes. Article PDF pages 114–117
and catalogue pages 9–10 were inspected. All 200 standard statements,
416 labels and existing numbers are unchanged. SymPy 1.14.0 verifies the
displayed elliptic expansion through exponent −9, its squared identity
to that order, the discriminant and the derivative at infinity; these
finite checks do not prove the ideal classification. The independent
inventory audit checks 3,759 results in 61 reports; all 4,301 cited source
references resolve and the 1,562 local Markdown destinations pass.
No Lean source changed in this review.

## Profinite and separation-topology synchronization

Merged upstream through `efc5446`, including the profinite topology work
in `4a5bc50` and the arithmetic separation homeomorphisms. The ordinary
congruence inverse limit now has its product-subspace topology, with
compactness for finite residues, Hausdorffness, total disconnectedness
and a dense canonical map. The actual omnific-to-integer comparison is
both a ring isomorphism and a homeomorphism, and the canonical map from
the congruence topology is dense inducing; its kernel remains `Π`.
The ordinary and prime-adic separation quotients are likewise homeomorphic
to `ℤ` with their respective arithmetic topologies. The separate
uniform-space completion comparison and the prime-adic completion
homeomorphism remain **Pending**. None of these arithmetic results
formalizes the geometric arguments reviewed above.

No manuscript source changed in this merge. The new generic topology
modules and their actual omnific instantiations were read against the
updated implementation mappings. With no other Lean process active,
`LEAN_NUM_THREADS=2 lake build` passes all 4,422 jobs; the axiom audit
passes 15,076 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. The independent inventory checks 3,759 standard results
across 61 reports, all 4,301 cited source references resolve, and all
1,567 local Markdown destinations across 185 files pass. The article
and catalogue remain the previously validated 180/32-page versions.

## Large-cardinal and independent-copies synchronization

The next publication attempt encountered upstream through `ce272a7`.
The merge is documentation-only: `de45cee` assembles the three
large-cardinal manuscripts, `781b19e` writes the single independent-copies
manuscript, and `aa268a4` delivers nine further archives awaiting placement.
The index now includes all 76 standard environments of the large-cardinal
report, replacing the base's 32, and refreshes the independent-copies
report's 29 entries and its three additional main-theorem references to
their `isc:` labels. Its 34-page PDF and the new 80-page large-cardinal PDF
are present. All 61 reports now have PDFs; the catalogue, reader map and
root README no longer describe the large-cardinal write as pending.

The newly added same-reals inner-model application in
`dsn:rem:largecardinal` points to `lce:lem:absolute`. Its scope and the
large-cardinal and independent-copies additions remain pending independent
proof review, source reconciliation and Lean formalization. No existing
mapped theorem changes in this merge. This record verifies navigation
and integration, not the incoming proofs or their imported foundations.

The independent inventory passes for 3,803 standard results in 61 reports,
including 3,784 labeled and 19 unlabeled entries. All 4,347 cited source
references resolve and all 1,575 local Markdown destinations pass.
The catalogue builds in three passes to 32 pages without warnings or bad
boxes; its changed entries on pages 11 and 32 were inspected. No Lean
source changed, so the preceding 4,422-job build and 15,076-declaration
audit apply without another build. The Diophantine review boundary and
its validated 180-page article are unchanged.

## Singular-curve and automatic-summability integration

Merged the next upstream publication through `889b87c`, including
`1ad4ad8` (Diophantine source C16) and `d4d72d7` (automorphism source 14).
The Diophantine report now has fourteen manuscripts and 217 standard
results; the automorphism report has nine manuscripts and 140 standard
results. The ledger adds all seventeen singular-curve results and six
automatic-summability results. The catalogue and reader map now describe
these additions without treating their mathematical review as complete.
The six other batch-31 companions still await integration.

The merge preserves every one of the previous 200 Diophantine statements
and 134 automorphism statements, apart from source-credit additions.
The projective-coordinate proof corrections survive intact. The index
conflict was resolved from the current sources, and the Diophantine PDF
conflict by rebuilding the merged article. All existing Diophantine label
numbers are unchanged. The three-pass article build has 198 pages, with
no warnings, unresolved references or bad boxes; pages 117–118 at the
reviewed/unreviewed transition were inspected. The catalogue builds cleanly
in three passes to 32 pages, with the changed continuation pages inspected.

The independent inventory passes for 3,826 standard results across 61
reports, including 3,807 labeled and 19 unlabeled entries. All 4,370 cited
source references resolve and all 1,575 local Markdown destinations pass.
No Lean source changed; the passing 4,422-job build and 15,076-declaration
audit remain applicable. Sections 17.5–17.6 and 18 of the Diophantine report,
the new automorphism arguments and remaining imported foundations still
need independent proof review. In particular, indexing the normalization
criterion does not justify using a normalization lift without proof.

## Prime-adic topology and finite-test synchronization

Merged upstream through `cb55b52`: `8eee62a` proves the prime-adic
completion homeomorphism, and `9b463f7` adds quotient source 22 on finite
tests at new scales. The topology proof compares residue neighborhoods
with Mathlib's existing metric on the p-adic integers. Its canonical map
is dense inducing with the same constant-term formula and kernel. The
generic topology modules and actual omnific instance were read against
the ledger; `LEAN_NUM_THREADS=2 lake build` passes 4,427 jobs and the axiom
audit passes 15,107 declarations using only `propext`, `Classical.choice`
and `Quot.sound`. The separate uniform-space completion comparison remains
pending, but both inverse-limit topological identifications are now proved.

The quotient report now assembles nineteen manuscripts, with 277 standard
results and nine separately styled main theorems. The twelve new standard
results and the expanded `osq:main:polynomial` remain pending independent
proof review and Lean formalization. The earlier standard statement bodies
are unchanged; only source credits are added. The reader map, catalogue
and ledger reflect the new scope and the five remaining batch-31 companions.
The independent inventory passes for 3,838 results in 61 reports; all
4,382 cited source references and 1,578 local Markdown destinations resolve.
The catalogue again builds cleanly in three passes to 32 pages, and its
updated quotient entry was inspected. No Diophantine source or review
boundary changed in this merge.

## Support-bound and fraction-clearing synchronization

Merged upstream through `0b71362`, including the actual-surreal support
bounds and fraction-clearing proofs in `49da84e`. The new module and its
mappings were checked against `odg:lem:setbounds`, `odg:thm:commondivisor`
and `odg:thm:fractions`. Smallness is explicit in the carrier's lower
universe, and the bounding exponent may leave a fixed Hahn workspace.
The resulting `IsFractionRing` instance identifies the actual surreal
field as a fraction field of its omnific subring. This adds no geometric
normalization-lifting or projective-ideal coverage.

`LEAN_NUM_THREADS=2 lake build` passes 4,428 jobs; the axiom audit passes
15,123 declarations with only `propext`, `Classical.choice` and `Quot.sound`.
No manuscript or PDF changes in this merge. The independent inventory
still verifies 3,838 standard results in 61 reports, all 4,382 source
references resolve, and all 1,581 local Markdown destinations pass.

## Singular-curve normalization and conductor review

The Diophantine proof review now covers Section 17.5 and Sections
17.6.1–17.6.5, through the polynomial witness in every fiber. It reviews
eleven standard results: the classification, finite power identity,
conductor certificate, derivative-order bound, boundary place, one-place
obstruction, positive genus and four structural consequences. The
repeated-root and arithmetic applications remain unreviewed.

The corrections distinguish failure of normality from an actual failed
curve lift, and normality in the fraction field from integral closure in
a larger Hahn field. A nonconstant curve point over `𝕜[ω]` does lift;
the displayed square root outside `𝕜(ω)` cannot obstruct it. The
contracted differential need not belong to the function field. Its
valuation is nevertheless commensurable with the conductor's, by the
chosen Euler derivative of a uniformizer. The revised proof constructs
the conductor, explains the fixed multiplier and order-zero identity,
gives the finite one-place bound, and expands coefficient descent and
polynomial-fiber nonconstancy.

The nonzero-group convention is explicit in the singular subsection and
in the dimension-one theorem: `Γ=0`, `X=𝔸¹` refutes that equivalence
without the guard. All other standard statements, all 471 labels and
their existing numbers are preserved. Targeted comparison with source
C16 and primary checks of Seidenberg's argument and the relevant
normalization, valuation and differential inputs are recorded in the
report reconciliation. This adds no Lean coverage.

The article and catalogue build in three passes to 199 and 32 pages with
no warnings, unresolved references or bad boxes. Affected normalization,
conductor and structural pages and the catalogue entry were inspected.
The independent inventory verifies 3,838 standard results in 61 reports;
all 4,382 cited source references and 1,581 local Markdown destinations
resolve. The root README, notation guide and review boundaries agree
with this scope. No Lean source changed in this review.

## Singular-review integration and automorphism wording

The singular-curve review was committed as `860b622`; the subsequent merge
includes upstream work through `336b216`. The incoming Lean results cover
the purely infinite ideal, its completion and nilpotent tests, and omnific
irreducibles and failure of atomic factorization. Their mapped source
statements were reread. The combined `LEAN_NUM_THREADS=2 lake build` passes
all 4,432 jobs; its axiom audit passes 15,186 declarations using only
`propext`, `Classical.choice` and `Quot.sound`.

The six incoming main-text changes preserve all their earlier labeled
standard and principal theorem statements. The holonomic addition has 33
new standard results and two new principal theorems. The reader map, root
README and catalogue now reflect the written order-two obstruction,
third-order obstruction through cubic jet degree, and relative-scale
criterion for mixed linear equations. The latter retains the condition
that no quotient of distinct multipliers is a root of unity and concerns
existence of some operator, not solvability of a prescribed one. These
chapters remain pending independent proof review and Lean formalization.
The catalogue entry now groups the mathematics by subject instead of
recounting each manuscript's arrival. The three unintegrated companions
and nine newly placed manuscripts have their current status recorded.

A targeted correction to `opa:as:cor:invisible` and its reciprocal status
note at `osq:q:invisible` distinguishes an automorphism of `Oz` from its
extension to `No`: it is the extension that fixes all ordinary reals.
Preserving constant coefficient is written `ct ∘ σ = ct`. The same two
passages now apply `u` before the monomial map in `M_{χ,τ} ∘ u`; the earlier
corollary described the order in reverse. These changes match the cited
extension and factorization theorems. They do not constitute a proof review
of automatic strongness or the factorization theorem. The notation guide
records both distinctions. All 316 automorphism-report labels and 551
quotient-report labels remain in order; only that corollary's statement
changes, and no labels or source-index line numbers move.

The corrected automorphism and quotient PDFs build in three passes to 104
and 177 pages, and the revised catalogue to 32 pages, with no warnings,
unresolved references or bad boxes. The affected passages and catalogue
entry were visually inspected. The independent inventory verifies all
3,871 standard results across 61 reports; all 4,416 cited source references
and 1,588 local Markdown destinations across 197 files resolve. This
integration validation leaves the review boundaries stated above intact.

The final synchronization also includes `ea802cc`, formalizing projective
clearing and simultaneous common multiples of all ordinary powers. The
source corollary and both new modules were checked for the distinction
between a small family and the whole proper class; homogeneous rescaling
does not assert primitive coordinates. The combined build passes 4,434
jobs and the axiom audit passes 15,193 declarations with the same three
axioms. All 4,417 cited source references and 1,590 local Markdown
destinations resolve. This merge changes no report source or PDF.

## Repeated-root and singular arithmetic application review

The Diophantine review now reaches Section 17.6.8, covering six further
standard results: the superelliptic and quadratic-root criteria, the
pinched elliptic example, omnific rigidity, arithmetic families and the
Gaussian existence dichotomy. The source comparison and exact boundaries
are recorded in the report reconciliation.

The merged superelliptic theorem omitted C16's irreducibility assumption.
The polynomial graphs of `Y²=X²` refute the criterion without that guard.
The assumption is now explicit in the setup and theorem, and the adjoining
explanation has the correct direction of the power-divisibility condition.
The ramification calculation now distinguishes finite-root multiplicities
from the negative exponent at infinity, computes each branch and explains
why precisely the points over infinity are omitted. The normalization
parameter is recovered in the function field by an integer Bézout identity.

The pinched elliptic proof verifies its conductor and displays each term
cleared by `x³`; its seventh-order valuation contradiction and derivative
count are explicit. Arithmetic families now check the defining equations,
allowed coefficients, finite support and proper-class distinctness. The
Gaussian argument supplies the normalization-preimage step. The real
isolated node with only `±i` over its origin illustrates the limitation
without claiming that every possible Hahn point in that fiber is excluded.
The notation guide, reader map, root README and catalogue have matching scope.

All 217 standard statements remain, with only the superelliptic hypothesis
changed. All 471 labels and their numbers are preserved. The corrected
article and catalogue build in three passes to 200 and 32 pages without
warnings, unresolved references or bad boxes; the application pages and
catalogue entry were visually inspected. The preserved C16 finite suite,
run on a copy, passes all 113,940 assertions. Its full JSON record matches
the delivered one apart from Python 3.13.5 becoming 3.13.14 and runtime.
It checks identities and bounded examples, not the geometric or infinite
claims. The independent inventory verifies 3,871 results in 61 reports;
all 4,417 cited source references and 1,590 local Markdown destinations
resolve. No Lean source changed; the preceding 4,434-job build and
15,193-declaration axiom audit remain applicable. These six results are
still **Pending** in Lean, and the broader proof review remains incomplete.

The subsequent synchronization through `7b256e0` adds ordered omnific
division, the nonterminating Euclidean sequence and irrational pairs without
a gcd. Their source statements and four new modules were checked for the
positive-divisor guard, ordinary finite iteration and divisibility meaning
of gcd. The combined `LEAN_NUM_THREADS=2 lake build` passes 4,438 jobs;
the axiom audit passes 15,245 declarations with only `propext`,
`Classical.choice` and `Quot.sound`. All 4,419 cited source references and
1,594 local Markdown destinations resolve. This merge changes no report
source or PDF and leaves the application review's scope intact.

The last fetch also merges delivery `51c1cc7`: nine ZIP archives, all passing
ZIP integrity checks and each containing an article source. They await
placement, integration and review. No maintained report source, PDF or Lean
file changes, so the existing inventory and build validation remain
applicable. Archive integrity is not a mathematical review.

## Group varieties and coefficient algebras review

The Diophantine review checks the closing singular-curve scope notes and
all thirteen standard results in Sections 18.1–18.4. The proofs now show
how torus descent reflects equality, why finite coefficient bases give the
scalar-extension isomorphism, and how quasi-finite fibers reduce to finite
coordinate algebras. The commutative-group proof applies the product
structure theorem to its affine subgroup and writes the inverse maps for
the splitting of point groups. The Milne statement numbers and their
characteristic-zero and affine hypotheses were checked in the 2017 edition.

For reduced coefficient algebras, the closed equalizer ideal makes the
joint-injectivity argument explicit. A series over `k[s]` shows why the
natural tensor map need not be surjective; this does not imply failure of
flatness. Dual-number lifts are derived on charts and glued, and the
ordinary dual-number subgroup is tracked before taking the tangent-space
quotient. The characteristic-two example uses finite coefficient incidence,
not convergence of truncations. The discretely ordered-ring proof verifies
injectivity by parity of leading exponents and identifies the nonzero
element killed by any proposed unital embedding into the omnific integers.
The notation guide, reader maps, catalogue and root README reflect this scope.

All 217 standard results and 471 label numbers are preserved. The only
statement-text change defines dual numbers unambiguously as `S[T]/(T²)`.
Three-pass builds give a 201-page article and 32-page catalogue, without
warnings, unresolved references or bad boxes. Article pages 131–138 and 201
and catalogue page 9 were visually checked. The copied C11 finite suite
passes 13,049 assertions and its entire JSON output matches the delivered
record; it does not certify the geometric or infinite claims. The independent
inventory checks 3,871 results in 61 reports, and all 4,419 source references
and 1,596 local Markdown destinations resolve.

Synchronization through `9ee2dac` includes the two modules proving the
strict ascending ideal chain and failure of integral closure. Their mapped
statement and proofs were checked. The combined `LEAN_NUM_THREADS=2 lake
build` passes 4,440 jobs; the axiom audit passes 15,269 declarations with
only `propext`, `Classical.choice` and `Quot.sound`. No Lean source is changed
by this review. Its thirteen geometric and coefficient-algebra results
remain **Pending** in Lean. Sections 18.5–18.6, later scope notes and full
source reconciliation remain outside the completed manuscript review.

## Group-review synchronization and two new reports

The synchronization through `f388f95` includes the nine report expansions
through `c315ac9` and placement `aa9c891`. The former add 289 standard
results; their new proofs remain outside the completed review scopes.
Existing labelled standard statements change only in their source credits;
the separate `osq:main:closure` overview gains the cyclic-workspace claims.
None of those changed labels has an implementation mapping. All cited source
labels still resolve. The four incoming Lean modules implement polynomial
and positive-existential transfer, retraction closure and its definability
obstructions. Their native ring-language fragment, integer-parameter guard
and explicit positivity counterexample agree with the mapped Diophantine
statements. The combined two-thread build passes 4,449 jobs and the axiom
audit passes 15,345 declarations with only `propext`, `Classical.choice`
and `Quot.sound`.

Placement adds two main texts: continued fractions (26 standard results)
and exponential relations over omnific integers (34). The inventory now
includes 4,220 standard results across 63 reports. Seven companions have
audit, code and data files placed but main-text integration remains pending.
The catalogue, reader map and root README reflect the distinction. The new
package instructions use the actual `code/` and `data/` locations and no
longer advertise an omitted manifest. Their article sources and recorded
verification data are unchanged.

The missing PDFs build in three clean passes to 22 and 28 pages. Visual
checks cover their title and contents pages, continued-fraction pages 10
and 22, and exponential-relation pages 15 and 28. The continued-fraction
suite passes 81,256 assertions; its entire JSON differs only in the Python
version (3.13.5 to 3.13.14, with SymPy 1.14.0 unchanged). The exponential
suite passes 22,074 cases with identical JSON. These finite regression
checks are not an independent proof review of the new manuscripts.

The updated catalogue builds in three passes to 32 pages without warnings,
unresolved references or bad boxes; the opening pages, new entries and
family transitions were visually checked. Every one of its 63 main-document
destinations exists. The independent inventory audit passes; all 4,763
cited source references and 1,623 local Markdown destinations resolve.
The reviewed Diophantine source and its 201-page PDF are unchanged by this
integration. The new reports and all unreviewed additions remain pending
independent proof review and Lean formalization.

The final synchronization through `8a60159` also brings the chosen-Smith-
reduction criterion and all-solutions description. The two modules were
checked against `odg:thm:smith`: zero rows require the whole transformed
entry to vanish, pivots need ordinary constant-term divisibility, and the
free coordinates remain arbitrary. The combined two-thread build passes
4,451 jobs and the 15,361-declaration axiom audit, with the same three allowed
axioms. The polynomial-composition integration adds 18 standard results
and principal Theorem N; reciprocal notes in six neighbouring reports
change no existing standard statement. The refreshed inventory has 4,238
standard results in 63 reports. All 4,782 cited source references and 1,630
local Markdown destinations resolve. The new universal-symmetries archive
has eight members and passes ZIP integrity checks, but placement and review
remain pending. The reviewed Diophantine source/PDF and the catalogue are
unchanged by this final merge.

## Logarithmic rigidity and arithmetic descent review

The manuscript review now covers Sections 18.5–18.6 of the Diophantine
report, including its six logarithmic valuation, annihilation, tangent
separation, arithmetic descent, omnific specialization and product results.
Their statements and hypotheses are unchanged. The proofs now construct
the local normal-crossings logarithmic sheaf, compare contractions in the
common Hahn field, explain constancy from vanishing tangents and descend
equality through the closed diagonal. The class-sized specialization spells
out its finite-presentation workspace. A valuation-preserving derivation
counterexample explains why logarithmic derivative bounds are also needed.

The review corrects the claim that there are no ring maps between the two
rings: constant-extraction maps exist, but do not commute with their given
Hahn-field inclusions for a nontrivial exponent group. It also limits the
Stacks logarithmic-poles citation to its actual single-smooth-divisor scope
and adds the normal-crossings definition separately. The sign change for
Euler characters and the exponent group in a valuation-ring example are
explicit. The source C15 comparison and primary-source checks are recorded
in the report's reconciliation file; full parallel-source reconciliation
and later scope notes remain pending.

All 217 standard result environments and all 471 source labels are
preserved, as are the 942 auxiliary numbering entries. Three-pass builds
produce a 202-page article and 32-page catalogue without warnings,
unresolved references or bad boxes. Visual inspection covers article PDF
pages 137–144, 192 and 202 and catalogue page 9. The copied C15 verifier
passes 2,820 checks in seven groups; its full JSON differs from the delivered
record only in the Python version (3.13.5 to 3.13.14). Those finite checks do
not prove the scheme-theoretic or infinite Hahn-series assertions.

The independent inventory checks 4,238 standard results across 63 reports;
all 4,782 cited source references and 1,630 local Markdown destinations
resolve. No Lean source changes in this review. The six results remain
**Pending** in Lean; the previous combined build passed 4,451 jobs and its
15,361-declaration axiom audit. Incoming changes require their own subsequent
synchronization checks.

## Logarithmic-review synchronization

The merge through `737fa31` preserves all existing shared labelled standard
statements in the affected reports. The continued-fraction and exponential
reports now have written collection editions with prefixed labels; their
proofs remain pending independent review. The two dilation companions add
33 standard results, bringing the inventory to 4,271 across 63 reports.
The reader map and catalogue now distinguish those integrated companions
from the five batch-33 companions whose main texts remain pending. Eight
new archives in `a4611ad` pass ZIP integrity checks; placement and review
remain pending. A duplicate reader-map row was removed.

The three incoming Lean modules were checked against `odg:thm:linear`:
constant extraction splits every solution with ordinary right-hand side,
any rational kernel basis gives unique purely infinite coefficients, and
full column rank forces all solutions to be ordinary. The rational action
is identified with multiplication in the actual surreal field. The combined
`LEAN_NUM_THREADS=2 lake build` passes 4,466 jobs and its axiom audit passes
15,404 declarations using only `propext`, `Classical.choice` and `Quot.sound`.

The merged Diophantine source retains all 217 standard statements and 942
auxiliary numbering entries. Its three-pass PDF has 202 pages; the updated
catalogue has 32. Both final logs contain no warnings, unresolved references
or bad boxes. Incoming cross-report notes change no standard statement;
their placement does not extend the completed proof-review scope. The
independent inventory passes, all 4,820 cited source references resolve,
and all 1,659 local Markdown destinations resolve. The incoming finite
verification programs and recorded data are unchanged; the C15 rerun and
its limited scope are recorded above.

The final synchronization through `4d7b779` adds five modules for
`odg:lem:constantproduct` and both clauses of `odg:thm:decomposable`.
Their statements were checked against the manuscript: nonzero levels and
positive multiplicities are retained, real omnific variables use the real
kernel of the complex forms, arbitrary complex support-ring variables use
complex column rank, and the coefficientwise description uses actual Conway
coefficients. The combined two-thread build passes 4,471 jobs and its axiom
audit passes 15,460 declarations with the same three allowed axioms. All
4,821 cited source references and 1,665 local Markdown destinations resolve.
The 4,271-result inventory passes. No TeX source or PDF changes in this last
merge; the preceding render checks still apply. The Gaussian fiber and
converse existence statements remain pending in Lean.

## Workspace and closing-scope review

The Diophantine scope pass checks Section 20 and Sections 21.1–21.6 against
the maintained proofs and implementation ledger. It corrects the unconditional
claim about products with the affine line, distinguishes singleton rigid-curve
fibers from affine-line fibers, and distinguishes vanishing Euler contractions
from vanishing differential forms. The integer-exponent workspace supplies an
explicit counterexample to universal idempotence: `Π = ω ℝ[ω]` and
`Π² = ω² ℝ[ω]`. The arithmetic curve summary now states its real-fiber and
ordinary-point hypotheses. Rational-hull characters preserve original supports;
the scalar-representation theorem retains unimodularity. The fraction synthesis
states uniqueness up to sign, and the catalogue uses constant-term specialization
rather than standard part for that classification.

The formalization route is rewritten in dependency order at `38425db`, with
chosen Smith reductions, the real/complex kernel distinction and the remaining
logical and geometric obligations explicit. The proposed module table now
breaks over pages with repeated headers and preserves later table numbering.
The root README, notation guide and coverage records reflect this scope.
This is a check of maintained statements and their summaries, not completion
of parallel-source reconciliation or of imported classical foundations.

All 217 standard result environments, 30 question environments, 471 source
labels and 942 auxiliary numbering fields are preserved. Three-pass builds
give a 203-page article and 32-page catalogue without warnings, unresolved
references or bad boxes. Targeted visual inspection covers the changed scope
paragraphs, both roadmap pages, the closing fiber/synthesis text and catalogue
pages 9–10. The independent inventory passes for 4,271 results in 63 reports;
all 4,821 source references and 1,665 local Markdown destinations resolve.
No Lean source or finite verification program changes in this pass; the last
combined build was 4,471 jobs and its axiom audit covered 15,460 declarations.
Incoming synchronization is checked separately. Remaining pointers in Sections
1, 6, 7 and 14, Section 21.7, the appendix foundations and complete source
reconciliation remain pending.

## Scope-review synchronization and new manuscript boundaries

The merge through `31e3489` adds the Gaussian omnific ring and exact
Gaussian decomposable fibers (`4037368`) and both real and Gaussian kernel
converses (`ae0210c`). Their five modules were checked against
`odg:dec:thm:gaussianfibers` and `odg:dec:cor:converse`: constants lie in
Mathlib's Gaussian integers, kernel coefficients are actual Conway
coefficients, ordinary fibers are disjoint, and the converse retains an
ordinary point at a nonzero level. The generic nonzero-kernel argument uses
a supplied nonzero vector; its actual instantiation supplies the monomial
`ω`. The combined two-thread Lean build passes 4,478 jobs and its axiom audit
passes 15,506 declarations using only `propext`, `Classical.choice` and
`Quot.sound`.

The holonomic coefficient-observable addition (`76dd876`) adds eleven
standard results and principal Theorem O. Source C17 (`fdedce0`) adds 27
standard results to Section 19.4 of the Diophantine report and ten questions,
plus summary and provenance material. Existing holonomic standard statements
are unchanged; five existing Diophantine statements change only by adding
C17 to their credits. All thirty earlier question statements are unchanged.
None of this new manuscript material is included in the completed independent
review scopes, including its new paragraphs in Sections 20–21.6. The reader
map, catalogue and ledger now distinguish these integrations from the three
remaining batch-33 omnific-automorphism companions. Nine further companions
are placed in `a7a435f` with main texts still pending. The six-member Hahn-joins
archive delivered in `267b910` passes ZIP integrity checks but awaits placement.

The merged article builds in three passes to 225 pages and the catalogue to
33, with no warnings, unresolved references or bad boxes. Every earlier
auxiliary label retains its number. Visual checks cover the merged workspace
and roadmap pages, corrected product and contraction explanations, and the
updated catalogue entries and ending. The formalization route records the
new Gaussian/converse proofs; its geometric and discriminant obligations
remain pending. The independent inventory passes for 4,309 results in 63
reports; all 4,860 cited source references and 1,673 local Markdown
destinations resolve. Incoming finite suites were not rerun in this scope
review, and their delivered records are not treated as independent proofs.

## Fiber-size and automorphism synchronization

The next merge through `a80f112` brings the four kernel-line/size modules
from `827be60` and three binary-form/Pell modules from `782376e`.
Their statements were read against `odg:dec:cor:converse`, its following
examples, `odg:thm:binary` and `odg:cor:pell`. The fiber embeddings retain
an ordinary point, a nonzero level and a nonzero direction in the correct
real or complex kernel. Their size conclusion is explicitly relative to
Lean universes. The empty-fiber example proves why the ordinary-point
hypothesis is needed. The binary-polynomial theorem needs two independent
homogeneous linear divisors but no homogeneity hypothesis on the polynomial;
the Pell application covers all nonzero integer parameters and levels.
The combined two-thread build passes 4,485 jobs and the axiom audit passes
15,573 declarations with only `propext`, `Classical.choice` and `Quot.sound`.

The three remaining batch-33 companions are now integrated in the
omnific-automorphism report by `19d0b0e`. They add 89 standard results on
formal orbit fields, left-orderable symmetry groups and formal integration
of derivations, bringing that report to 274 and the collection to 4,398
across 63 reports. A comparison of statement environments finds all 185
previous statements unchanged and all previous labels retained. The new
claims, their imported class constructions and their complete source
reconciliation remain pending independent review and Lean formalization.
The later universal-symmetries companion remains staged. Reader summaries,
the root README and catalogue now reflect fourteen integrated manuscripts
and retain the conjugation condition on the complex group classification.

The independent inventory passes for all 4,398 results; all 4,950 cited
source references and 1,680 local Markdown destinations in 225 files resolve.
The revised catalogue builds in three passes to 33 pages without warnings,
unresolved references or bad boxes; its changed entry is visually checked
on pages 10–11. The 225-page Diophantine PDF and source are unchanged since
the preceding successful build. The delivered automorphism PDF is retained;
its new proofs and finite verification suites have not been independently
reviewed or rerun in this synchronization.

## Geometric pointers and neighboring-report comparison

At `39a46b7`, the Diophantine report's geometric summaries in Sections 1,
6, 7 and 14 and the cited statement scopes in Section 21.7 were checked
against the maintained theorems and neighboring reports. The opening now
retains nonzero levels, characteristic zero and nondegeneracy where the
cited statements require them. It explains that an `Oz` automorphism fixes
real numbers through its fraction-field extension. The curve summaries
retain nonzero exponent groups and geometric integrality. An affine-line
real fiber is distinguished from an affine-line model over the integers,
and the integer-point condition remains explicit. The commutative-group
kernel description no longer suggests an algebraic splitting.

The polynomial-arc pointer now gives the entire constant-term fiber in real
polynomial coordinates, distinguishing monomial finite-support witnesses
from arbitrary purely infinite parameters. The comparison of unit arguments
explains why a curve needs only one nonconstant unit: specialization forces
a nonzero prime kernel in its dimension-one coordinate ring. The general
affine argument instead requires generation by units.

The groups report's current remark already cites the curve classification;
its real singular arithmetic existence question remains open even though
the geometric normalization criterion is proved in the manuscript. The
comparison now states this boundary. It also distinguishes the rank-one
bounded-support GCD hypothesis from `Oz`, local Euler derivations from
full-class maps into set-sized modules, and the named-dilation language from
the pure-ring reconstruction. C17's translation comparison retains the
integer-valued and more-inputs-than-degree hypotheses; discreteness alone
is insufficient. Only this statement comparison and positive degree in
C17's opening summary were checked, not its proofs or remaining questions.
The guide, notation record, reader map and root README reflect these scopes.

All 244 standard statements and 553 labels are unchanged. The three-pass
article build has 225 pages, no warnings, unresolved references or bad boxes,
and preserves all 1,106 prior auxiliary label numbers. Visual checks cover
PDF pages 8–9, 70, 108 and 179–180. The independent inventory passes for
4,398 standard results in 63 reports; all 4,950 source references and 1,680
local Markdown destinations in 225 files resolve. No Lean source or finite
verification suite changed; the applicable combined build remains 4,485
jobs with an axiom audit of 15,573 declarations. Imported proofs, remaining
C17 material, appendix foundations and full parallel-source reconciliation
remain separate work.

## Comparison-review synchronization

The merge through `6bd00c0` adds the exact zero Pell fiber (`0d256fa`),
the rank-deficient Pell example (`5795c25`) and the real/Gaussian contrast
for `X + iY` (`91158f6`). Their three Lean modules were read against
`odg:prop:zeropell`, `odg:dec:ex:rankdeficient` and `odg:dec:rem:kernels`.
The zero-level theorem retains positive nonsquare `D`; the rank-deficient
parametrization handles any nonzero ordinary `D` and level. The Cartesian
form is rigid on real omnific pairs even at level zero, while the Gaussian
purely infinite line supplies the explicit nonordinary point. The combined
two-thread build passes 4,488 jobs, and the axiom audit passes 15,602
declarations using only `propext`, `Classical.choice` and `Quot.sound`.

Four batch-34 companions add 75 standard results: eighteen in dynamics,
fourteen in surcomplex real forms, twenty-eight in independent copies and
fifteen in Hahn–Hilbert geometry. Their earlier mathematical statements
and labels are retained. Twenty independent-copies statements acquire
explicit label types, with no mathematical change. This also preserves the
field-automorphism statements used in the completed comparison above.
All four additions await independent proof review and Lean formalization;
their delivered PDFs and finite verification records are retained without
claiming independent validation of the new mathematics. Five further
companions from `a7a435f` remain staged.

The ledger's independent inventory passes for 4,473 standard results across
63 reports, with all 5,027 cited source references and 1,689 local Markdown
destinations in 225 files resolving. The catalogue is refreshed for the four
expansions, along with the twenty/fourteen/five manuscript counts of the
quotient, preserving-automorphism and group reports. Its three-pass build
has 33 pages without warnings, unresolved references or bad boxes; the
changed entries are visually inspected. The reviewed Diophantine source
and its 225-page PDF are unchanged by this merge. These updates preserve
all pending proof-review, imported-foundation and source-reconciliation
obligations recorded above.

## Positive-exponent correction from the power-rigidity formalization

The next merge, `365bea6`, adds three modules proving equal-power rigidity,
reduction through a common exponent divisor and the positive-power
univariate step. It also formally proves the counterexample
`ω^0 − 0² = 1`, where `gcd(0,2) = 2` but one coordinate is infinite.
The maintained `odg:rem:powers` (alias `odg:cor:powers`) now states positive
ordinary exponents and a nonzero ordinary integer level, explicitly uses
positive quotient exponents, and includes the counterexample. Its formerly
overgeneral sentence about all exponent pairs now restricts the separated
result to `m,n ≥ 2`; at exponent one, `y = x^m − c` is a nonordinary family.
The question-status summary, root README and implementation ledger agree
with this correction. The corrected gcd statement is proved in Lean;
coprime separated equations remain pending there.

The combined two-thread build passes 4,493 jobs and audits 15,618 declarations
with only the three permitted axioms. The corrected article builds in three
passes to 225 pages without warnings, unresolved references or bad boxes;
PDF page 33 is visually checked. All 244 standard statements, 553 labels and
1,106 label numbers remain unchanged; the correction is to a remark and its
summary. The independent inventory passes for 4,473 results in 63 reports;
all 5,029 cited source references and 1,693 local Markdown destinations in
225 files resolve. The new manuscript expansions and other outstanding
proof-review obligations retain their previous status.

## Pell-two and class-residue synchronization

The merge through `f45cddd` retains the corrected power remark and adds
`c091c6e`'s ordinary and omnific Pell-two classification. The two modules
verify the fundamental pair `(3,2)`, identify natural powers with
`(3 + 2√2)^k`, and apply Mathlib's proved fundamental-solution theorem with
independent coordinate signs. This matches `odg:ex:pell2` and keeps the
index an ordinary natural number. The combined two-thread build passes
4,497 jobs; the axiom audit passes 15,636 declarations with only the three
permitted axioms.

The universal-symmetries/difference-equations companion (`50dde76`) adds
24 standard statements to the preserving-automorphism report; all 274
earlier statements and labels remain unchanged. The two quotient
companions (`97ff204`) add 53 standard statements, expand the principal
summaries `osq:main:internal` and `osq:main:polynomial`, and add one source
credit to `osq:if:prop:closed`. The remaining prior statements and labels
are unchanged. These expansions, including their class-choice and
semialgebraic claims, remain pending independent proof review and Lean
formalization. The quotient and preserving-automorphism reports now have
twenty-two and fifteen integrated manuscripts respectively. Seven of the
nine companions placed in `a7a435f` are integrated; two remain staged.

The refreshed independent inventory passes for 4,550 standard results in
63 reports. All 5,106 source references and 1,698 local Markdown destinations
in 225 files resolve. The revised 33-page catalogue builds in three passes
without diagnostics and its changed entries on pages 10–11 are visually
checked. This merge does not change the corrected Diophantine source or
its validated 225-page PDF. No incoming finite suite was rerun in this
synchronization, and the new manuscript proofs remain outside earlier
review scopes.

## Full-surreal Pell contrast synchronization

The merge through `b401f5d` adds `e6b654a`'s split-norm field algebra,
actual two-term normal-form calculation and canonical truncation theorem.
These three modules match the contrast following `odg:ex:pell2`: positive
real `D` and any nonzero surreal parameter give the rational Pell
parametrization; at a positive monomial parameter and nonzero ordinary real
level both coordinates have forbidden negative terms. Their canonical
positive-growth parts have norm zero, so truncation does not preserve the
original nonzero equation. The corrected power remark and the count of
seven integrated companions are retained when resolving the ledger overlap.
No manuscript source changes in this merge.

The combined two-thread build passes 4,500 jobs and audits 15,654 declarations
using only `propext`, `Classical.choice` and `Quot.sound`. The independent
inventory passes for 4,550 standard results across 63 reports; all 5,106
source references and 1,701 local Markdown destinations in 225 files resolve.
The preceding clean 225-page article and 33-page catalogue builds remain
applicable. Pending mathematical review and source-reconciliation scopes
are unchanged.

## Hahn-joins companion placement

The subsequent merge through `6ab9666` places the Hahn-joins companion in
`dec8d56`: three build/verification artifacts under independent surreal
copies replace the delivered ZIP. Its main text remains unintegrated and
unreviewed. No Lean, manuscript or catalogue source changed, so the
4,500-job build, 15,654-declaration audit and both validated PDFs remain
applicable. All 5,106 source references and 1,701 local Markdown destinations
still resolve. The ledger and reader map now record placement separately
from integration and proof review.

## Earlier omnific integration validation

Eleven omnific-integer manuscripts arrived in `f0b7f43` and were placed in
`be06fc8`, which was merged after the field-automorphism build. That was a
documentation-only merge: no existing mapped manuscript or Lean source
changed. At that placement, the two new reports contained only base
manuscripts 01 and 06, with nine companions still to integrate, obsolete
build filenames and no current PDFs. At that stage, the elementary Diophantine update supplied a partial
integration and maintained PDF; the quotient report and later comparison
were pending. The synchronization record above supersedes that status. At placement
the reader map, catalogue and ledger recorded 75
standard statements, bringing the inventory to 2,610 in 51 reports; the
quotient base's three `maintheorem` statements are additional claims outside
the standard-environment count. Proof review and formalization are pending.
The independent inventory audit passes for all 51 sources then present, and all
3,090 cited labels and 1,261 local Markdown destinations resolve. The
catalogue's 51 main-document destinations exist; its three-pass build has
28 pages and no diagnostics, and all pages were visually checked. The
previous 4,264-job Lean build remains applicable after this docs-only merge.

The first publish attempt encountered `220784a`, including the eight
cosine-fold modules in `4accabc` and an independent omnific inventory update.
The merge retains those mappings and the catalogue's 51-entry status,
correcting the incoming description that all eleven manuscripts had already
been merged into the two base texts. No manuscript source changed.
The combined `LEAN_NUM_THREADS=2 lake build` passed all 4,272 jobs; its
axiom audit passed 12,787 declarations with only `propext`,
`Classical.choice` and `Quot.sound`. All 3,091 cited source labels and 1,271
local Markdown destinations resolve, and the 51-source inventory audit
passes. This is integration validation, not a proof review of the new reports.

## Remaining scope

The current collection has 61 main texts. The synchronization record above
states the latest omnific review boundary and the remaining companion
integrations. Historical counts below identify the versions previously
reviewed; they do not replace the current inventory.

Batch 22, placed in `7b5f934`, was assembled in `68e2960` and catalogued
in `5d369a0`. Its two reports,
[first-kappa coefficients](surcomplex/first-kappa-coefficients/) and
[single-dilation Hahn support](surcomplex/single-dilation-hahn-support/), and
new sections of entire functions, holonomic rigidity, trigonometry, Euclidean
three-space and Hahn probability are now indexed from their written sources.
Their mathematical proof review and source reconciliation remain pending.
At that stage the collection had 49 assembled reports. The six gamma/zeta archives
delivered in `cafe42f` and placed in `e4f8848` were assembled in `7af7056` as
[gamma and zeta functions](surcomplex/gamma-and-zeta-functions/) and catalogued
in `087ee37`. The current merged source has 94 standard result environments,
replacing the provisional base manuscript's 25 and bringing the 49-source
inventory to 2,534 at that integration; the new holonomic corollary brings
it to 2,535. Mathematical proof review and independent source-claim
reconciliation remain pending; assembly and inventory inclusion do not
establish either. The retired archives remain in Git history.

The nine manuscripts placed in `d4e71b7` are grouped as
[birthday cutoffs](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
and [fields across universes](foundations-and-computation/surreal-fields-across-universes/).
The reports were assembled in `3a2d35d` and catalogued in `13cb68e`;
all nine manuscripts are now represented in the two written sources. Their
136 standard result environments remain indexed in the ledger. Mathematical
proof review and source-claim reconciliation for these two assembled reports
remain pending.

The newly assembled [vector and tensor fields](surreal/vector-and-tensor-fields/)
and [three-space](surreal/euclidean-three-space/) reports are now written and
catalogued, but await proof review. The
[field-automorphism report](surcomplex/surcomplex-field-automorphisms/)
has received the Sections 1–15 and Appendix B main-text review above;
remaining imports, original-source reconciliation and priority remain separate.
[Finite probability](surreal/finite-surreal-probability/) has received the
Sections 2–17 main-text review recorded above; remaining imports and
source/provenance reconciliation are pending. The measures and
trigonometry expansions are also assembled; their new claims remain outside
the earlier review scopes. Delivered verification and source-audit artifacts
remain historical evidence, not a substitute for that review.

Batch 19's [three-duals report](surcomplex/three-duals-of-hahn-vector-spaces/)
has now received the Sections 1–15 main-text review recorded above;
remaining imports/source reconciliation are pending. Its
[hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/)
report has now received the Sections 1–11 main-text review recorded above;
remaining imports/source reconciliation are pending. Its
[transcendence over bounded support](surreal/transcendence-over-bounded-support/)
report has received the Sections 1–10 and conditional Appendix A review above;
remaining foundational/source reconciliation and priority are pending.
[Matrix scaling](surreal/matrix-scaling-at-surreal-scales/) has received the
Sections 1–14 main-text review above; remaining foundational imports,
original-source reconciliation and priority are pending.
The nonscalar dynamics addition has received the source-10 review recorded
above; remaining foundational imports and source reconciliation are separate.
The holonomic report now has the source-10 nonlinear and source-11/12
coefficient-field main-text reviews recorded above, including the new mixed
fraction-field consequence. Its remaining foundational/source reconciliation
and formalization obligations are separate. The spectral additions have
the Part III Drazin and Part IV Fredholm main-text reviews above; their
remaining imports/source reconciliation and formalization remain pending.
The critical-potential main-text review now
covers Sections 35–42; remaining imports and source reconciliation are pending.
Their inclusion in the statement index does not extend an earlier proof-review
scope or establish Lean coverage.

All ten reports from the earlier September 22 integration have received the main-text proof
reviews recorded above, including both parts of infinite-dimensional
spectral theory and Sections 2–21 of Hahn–Tate uniformization. This does not
complete the imported-result and source-reconciliation work.
The expanded differential-equations report has now also received a
main-text review of the complete regular-singular part, Sections 23–28.
The autonomous pass now covers the normalized-derivation foundations, curve-realization classification, finite-scale localization, derivation independence and worked equations (Sections 29–32), plus the holomorphic-differential and hyperelliptic obstructions (Section 33.1). The formal-group and abelian proofs of Sections 33.2–33.4 are now also reviewed, including the speed threshold for every normalized derivation. Section 34's scope, input contracts and formalization comparisons have now also been reviewed, completing the Part VI main-text pass. The critical-potential main-text review now covers Sections 35–42, including the tower, Euler classification, earlier-scale precision, three differential Hahn fields, Borel group and Schwarzian coordinates. Remaining imports and source reconciliation still require review.
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
critical-potential main text is also reviewed, while remaining imports and
source reconciliation are still separate.

Continue with elementary statements and their dependencies before broad
classification theorems. For each portion, check definitions and size/domain
hypotheses, reconstruct abbreviated arguments, inspect downstream uses of any
correction, align terminology with the guide, and rebuild the affected document.
A source-to-merged-claim reconciliation is still required where a report's
provenance account alone does not establish equivalent scope.


## Omnific Diophantine geometry — first discriminant proof review: elementary lemmas and translation

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


## Synchronization with norm forms and the final batch-34 companions

Merged `5003bcc`, including the number-field norm formalization and the
last two batch-34 companions. The norm implementation was compared with
`odg:thm:norm`: arbitrary rational bases, nonzero rational levels and
integer coefficients for bases of algebraic integers are all retained.
The full two-thread Lean build passes 4,511 jobs and audits 15,697
declarations with only the permitted axioms.

The quotient report now assembles 24 manuscripts, with 415 standard
statements and three principal summaries. Its polyhedral-cone and
henselian-branching companions add 52 standard results. Only the principal
summaries `osq:hd:main:cores` and `osq:main:closure` acquire new clauses;
all earlier standard statements are unchanged. The new mathematics and
the expanded summary clauses remain pending independent review and Lean
formalization. All nine batch-34 companions are now integrated, contributing
204 standard results; the separate Hahn-joins companion remains staged.

The collection index and summaries now report 4,602 standard results across
63 reports. The index conflict was confined to line anchors and resolved
against the merged source. All 5,159 source references and 1,723 local
Markdown destinations resolve. The catalogue was rebuilt in three passes
to 33 pages with no warnings, unresolved references or bad boxes. The
227-page Diophantine article and its reviewed proofs are unchanged by this
merge; no incoming finite verifier was rerun.


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
visually. The 4,602-result index, 5,160 source references and 1,723 local
Markdown destinations pass before this review record is appended. No Lean
source or finite verifier changed; this pass does not rerun the previously
passing finite suite or claim that it verifies the étale proofs.


## Synchronization with cubic norm rigidity and Hahn joins

Merged `8105a52`, preserving the finite étale review and the incoming
henselian-branching pointers. Those pointers were compared with the cited
local-ring, branching and forced-complexification statements; this does
not establish their proofs. The cubic norm implementation was compared
with the displayed example after `odg:thm:norm`, including the actual
omnific and Gaussian omnific carriers and nonzero ordinary levels.
The full two-thread Lean build passes 4,513 jobs and audits 15,719
declarations using only the three permitted axioms.

The independent-copies report now integrates its third manuscript, Hahn
joins, in Sections 28–41. It adds 24 standard results and four separately
styled main theorems; all 57 earlier standard results and all three earlier
main theorems are unchanged. The 81 standard results and seven main
obligations are recorded in the ledger. This new mathematics remains
pending independent proof review and Lean formalization. The collection's
current standard-result count is 4,626 across 63 reports, and the old
staged-companion notes have been updated.

The merged Diophantine article builds in three passes to 228 pages with
no warnings, unresolved references or bad boxes. All 244 standard
statements agree with the preceding review commit, and all 553 source
labels and 1,106 auxiliary label numbers are preserved. The revised
33-page catalogue is likewise clean; changed pages were inspected.
The independent index, 5,188 source references, 1,726 local Markdown
destinations and whitespace checks pass. The finite verification scripts
are unchanged and were not rerun during this synchronization.

## C17 monogenic descent, critical points and normal matrices

This pass reviews the maintained Section 19.4 from
`odg:disc:thm:monogenic` through the splitting-algebra second proof,
including its eight standard results, comparisons and boundary examples.
Together with the previous two passes, the main C17 theorem package has
been reviewed. Its later question/status notes and full reconciliation
against the parallel source manuscripts remain pending; these are distinct
from reviewing the maintained proofs. No C17 Lean coverage is claimed.

The monogenic proof now supplies the local square-matrix argument, the
trace-pairing/Vandermonde identity, explicit inverse translations and the
base-change presentation. The discriminant criterion is the finite locally
free criterion in [Stacks 0BJF](https://stacks.math.columbia.edu/tag/0BJF).
Zero algebras and the monic degree-zero polynomial are treated separately;
the empty-product discriminant is one in degrees zero and one. Arithmetic
descent uses a perfect trace pairing when the discriminant is a unit, and
the tensor-product presentation requires no flatness hypothesis.

The critical-point proof applies translation over the coefficient field's
one-sided ring, where division by the degree is allowed. It explains why
the residual constant is purely infinite. Critical gaps lie in the
algebraic closure of the coefficient field; simple critical points may
have repeated critical values. The sibling comparison was checked against
`osq:or:thm:canonical`, `osq:or:thm:eta` and `osq:or:thm:targets`: positive
degree is retained for canonical translation, degree at least two for rich
targets, and the ordinary target is explicitly Z or Z[i] in its arithmetic
case. This is a comparison of statements, not a new review of those proofs.

The matrix theorem now requires size at least one for its trace formula.
The projection proof derives orthogonality directly from idempotence and
normality, then bounds the entries. The spectral-projector proof explains
interpolation modulo the characteristic polynomial, the empty product in
size one, and commutation with adjoints with conjugated scalar coefficients.
The ordinary unitary diagonalization follows by taking constant terms.
The two-sided-support counterexample now rationalizes its small root,
making the infinitesimal coefficient explicit. The splitting-algebra
induction gives its base cases and free rank n!, and the second proof
explains why root differences stay nonzero in a generic field factor.

Validation: 51 assertions passed with SymPy 1.14.0 in the unchanged finite
resultant/critical-point and matrix/boundary groups (8 resultant, 18 critical,
1 example, 9 matrix, 7 counterexample and 8 positive-characteristic checks).
These do not certify arbitrary-support, descent or positivity arguments.
All 244 standard results and 553 labels are retained; the matrix size is
the only changed standard statement. All 1,106 auxiliary label numbers
are preserved. Three-pass builds of the 228-page article and 33-page
catalogue have no warnings, unresolved references or bad boxes; changed
pages were inspected visually. The 4,626-result index across 63 reports,
5,188 source references and 1,726 local Markdown destinations pass before
this record is appended. No Lean file or finite verifier was modified.

## Synchronization with finite étale norm and Hahn polynomial rigidity

Merged `1529c2d`, including the finite-product norm forms, rigidity for
actual omnific and Gaussian omnific coordinates, and the general Hahn
intermediate-ring theorem. The theorem statements were compared with
`odg:dec:thm:etale`: arbitrary bases and possibly different factor degrees
are allowed, constant levels are nonzero, and the intermediate ring needs
its stated intersection with constants, not a constant-term retraction.
The new polynomial-degree module covers arbitrary coefficient fields,
including positive characteristic, with no divisible-group assumption.
These incoming proofs cover earlier source labels; they do not formalize
the C17 descent or matrix package reviewed above.

The batch-35 reciprocal notes in five reports are retained. Their source
statements and the one-step conclusions were compared: primality with
constant coefficient one, distinct principal prime ideals and class
quotients, maximal transcendence over the specified Hahn composita,
strong/omnific automorphism restrictions, and the binary branch-code
shift. This does not review the underlying new Hahn-join proofs. All
standard and separately styled principal statements in the five changed
reports, and all their source labels, are unchanged by this merge.

The full build with `LEAN_NUM_THREADS=2` passes 4,520 jobs; its audit checks
15,778 declarations and uses only `propext`, `Classical.choice` and
`Quot.sound`. The combined Diophantine article builds cleanly in three
passes to 228 pages, preserving all 1,106 auxiliary label numbers; the
incoming note was checked visually. The catalogue source is unchanged by
the merge. The 4,626-result index across 63 reports, 5,189 source references,
1,735 local Markdown destinations and whitespace checks pass before this
record is appended. The unchanged finite suite was not repeated for this
synchronization.

## C17 question/status notes and elementary consequences

Reviewed the C17 notes in Section 19.4.11–12, the roots/coefficient status
paragraphs, all ten C17 questions and their explanations, and the C17
assembly/nonclaim summaries. This completes the maintained C17
question/status pass, not full reconciliation of the parallel manuscripts
or a literature search certifying the questions as open. The ten question
statements and all 244 standard theorem statements are unchanged.

The full-descent question now separates two issues. Full faithfulness of
base change follows from `odg:disc:prop:constants`: the algebraic constants
of A tensor D are exactly D by the dimension bound, so every map between
constant base changes restricts uniquely to a map over the coefficient
field. Existence of descent for every finite étale A-algebra remains
unproved. The arithmetic case is still separated from the field case.

The spectral-module note now splits the ordinary polynomial over the
algebraic closure before describing rank-one eigenmodules, and limits
positivity to the complex setting. Its explicit shear similarity shows
that the triangular nonnormal example has free eigenmodules; it is not
evidence for a nontrivial Picard group. The certificate note specifies its
index range, and the quantitative-defect note retains nonzero discriminant
so root velocities and denominator formulas are defined.

A sufficient inheritance criterion now answers a subcase of the
restricted-ring question. A subring of the one-sided coefficient ring
closed under constant extraction and division of purely nonconstant parts
by positive integers inherits translation from the ambient theorem and
its unique shift formula. Euler closure is not an extra assumption for
that deduction; no effective equality procedure follows from it.

The dynamics note proves an exact elementary consequence. Under the
critical-point normal form, in degree at least two, affine conjugacy in
the Hahn splitting field to a polynomial over the algebraically closed
coefficient field exists exactly when beta equals h. For L(X)=aX+b,
the leading coefficient forces a to be constant, the next coefficient
forces b-h to be constant, and the constant coefficient forces beta-h to
be constant. Its purely infinite support then makes it zero. Conversely
L(X)=X+h gives the ordinary polynomial. This does not classify iteration
or other notions of dynamical equivalence. The proof and the other new
deductions are marked as review additions, not attributed to source C17.

The Lean-status wording now acknowledges the shared ring, unit, degree
and algebraic-constant prerequisites already mapped in the ledger, while
keeping the C17 certificate, translation, étale-unit and matrix theorems,
and these new deductions, pending. The root README, catalogue, report
guide and notation guide reflect this distinction.

Validation: 26 scratch SymPy 1.14.0 assertions check the displayed affine
coefficient/conjugacy identities in degrees 2–7 and the shear similarity
and determinant. They are finite sanity checks, not proofs of general
support or descent. Three-pass builds of the 229-page article and 33-page
catalogue have no warnings, unresolved references or bad boxes; the
changed pages were inspected. All 553 labels and 1,106 auxiliary label
numbers are unchanged. The 4,626-result index across 63 reports, 5,192
source references and 1,735 Markdown destinations pass before this record
is appended. No Lean source or shipped verifier changed; the prior full
Lean build remains the baseline for this documentation-only revision.

## Synchronization with the quadratic ideal formalization

Merged `eef9d87`, including `3480bd8`. The incoming declarations were
compared with `odg:def:thm:ideal`, `odg:def:cor:idealhom` and the
other-radicand variant: the general theorem uses the full coefficient
pullback, a root in the coefficient field and a radicand nonsquare in the
fraction field of the constant ring. The actual omnific and Gaussian
omnific predicates are literally `∃ y, x² = 2y²`. Unital homomorphisms
preserve their witnesses without injectivity, size constraints or a
requirement to fix a chosen square root or imaginary unit. The incoming
root README and ledger entries are preserved; C17-specific coverage is
unchanged.

The full `LEAN_NUM_THREADS=2 lake build` passes 4,524 jobs, with 15,801
declarations passing the audit using only the three permitted axioms.
No article or catalogue source changed in this merge, so their validated
229-page and 33-page PDFs remain current. The source-label audit finds
5,194 references with none missing; all 1,739 Markdown destinations and
the 4,626-result index across 63 reports pass, as do whitespace checks.

The first push was rejected because `main` advanced. A further merge of
`ff5b5ad` adds formal proofs of both displayed quadratic-definition boundary
examples: the generated integer-polynomial subring has a purely infinite
generator without a quadratic witness, while adjoining sqrt(2) to the
constant ring supplies a nonzero constant witness. The generic range
statement is also instantiated at the integer-exponent Hahn monomial
`t^(-1)`. The two-thread full build now passes 4,526 jobs and audits 15,827
declarations with the same permitted axioms. Article/catalogue sources
remain unchanged; the index, 5,194 source references, 1,741 Markdown
destinations and whitespace checks pass after this merge.


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

# Sources and provenance for Report 292

## Mathematical record

The complete proof of the elementary-three classification, indicator obstructions, geometric gluing in arbitrary dimension, and the weighted cut value is in Report292.tex. No external mathematical theorem is required for these results. The sharp complex-quartic proof and cut-energy calculation are a self-contained specialization of the preceding Report291 manuscript.

Frozen Report291 title: The Sharp Weighted Energy Gap and Three-Coset Extremizers, prepared for Vladimir Reshetnikov, 7 October 2026.

- TeX SHA-256: ccdf8f7a0bb3242d663d5f146d8c7541a66796c740f55b6ba8905c5782461ad5
- Actual ZIP SHA-256: 0ebb59db8ece5d04467eefcc14aca4f4b7e4765ecf71d70b2366f205148537f8

The preceding report is not downloaded or needed during reproduction. Earlier reports remain unchanged. Its arbitrary-source classification is not being extended by assumption to the present endpoint; the present elementary-three argument proves its own complete classification.

## Builder provenance

build.py and tests/test_build.py are identity-only adaptations of the frozen Report291 public files. Report names/numbers, archive root, and archive basename are changed to Report292 and report292_nine_point_rigidity.zip. Guarded filesystem operations, bounded subprocess handling, source-immutability checks, deterministic ZIP metadata and resource ceilings are preserved. The companion and companion tests are a new exact finite implementation.

## Exact authored inventory

1. README.md
2. REPRODUCING.md
3. SOURCES.md
4. Report292.tex
5. build.py
6. companion/__init__.py
7. companion/README.md
8. companion/exact_checks.py
9. tests/test_build.py
10. tests/test_companion.py

The PDF makes eleven public files. MANIFEST.sha256 lists those eleven and does not list itself; the archive has twelve entries in total. Compilation logs, validation receipts, page images, exploratory outputs and review working documents are excluded.

## Primary literature inspected

The comparison is bounded and establishes no priority claim. All URLs below are primary paper, author, publisher or DOI records. The report's proofs remain self-contained; these sources provide context and attribution, not hidden premises.

### Affine target colorings

Matthew Mizell and James Oxley, Matroids Arising From Nested Sequences of Flats In Projective And Affine Geometries, Electronic Journal of Combinatorics 31(2) (2024), P2.48.

- https://doi.org/10.37236/12183
- https://www.math.lsu.edu/~oxley/EJC_Targets.pdf

Inspected target definitions, Theorem 4, restriction closure in Proposition 14, the proper-flat conclusion in Lemma 19, and the proof of Theorem 4. Their finite-dimensional ternary affine-target theorem is broader than the hyperplane-section situation used here. Under our stronger plane-section hypothesis, each plane coloring is a target, so their theorem makes the global coloring a nested-flat target. One color lies in a proper affine flat; the section restriction forces it to be line-closed and then of codimension one. This reduction is our comparison argument, not their theorem wording. The direct proof in this report is shorter and includes infinite dimension. No priority claim is made for that elementary geometry lemma.

### Majority correction in homomorphism testing

Michael Ben-Or, Don Coppersmith, Mike Luby and Ronitt Rubinfeld, Non-Abelian homomorphism testing, and distributions close to their self-convolutions, Random Structures & Algorithms 32 (2008), 49-70.

- https://people.csail.mit.edu/ronitt/papers/convd.pdf
- https://doi.org/10.1002/rsa.20182

Inspected Section 2, Theorem 1 and Lemmas 1-2, including the majority correction and three-event union-bound proof on author-PDF pages 3-5. The method of recovering a homomorphism by simultaneous dominant-derivative identities is established. The present shorter plane proof does not need majority repair: one high derivative directly supplies the two-row witness. The global common-kernel derivative comparison in this report is an exact geometric argument rather than a uniform-error repair theorem. This source was inspected as methodological context, not used as a proof dependency.

### Affine-invariant property testing

Arnab Bhattacharyya, Eldar Fischer, Hamed Hatami, Pooya Hatami and Shachar Lovett, Every locally characterized affine-invariant property is testable, STOC 2013.

- https://arxiv.org/abs/1212.3849
- https://arxiv.org/pdf/1212.3849
- https://doi.org/10.1145/2488608.2488662

Inspected Definitions 1.1 and 2.1, Section 1.2, and Theorems 1.2, 1.7 and 1.13; did not audit the full proof. Theorem 1.2 provides q-query proximity-oblivious testing for q-locally characterized affine-invariant properties over a fixed prime field and fixed finite alphabet. Applying it to this report's finite set of forbidden plane labelings gives a nine-query consequence for each fixed finite abelian H, with a positive distance-dependent rejection function. It does not give an explicit rate, a constant-success nine-query tester uniformly over all distances, a uniform bound over H, or an infinite-dimensional uniform sampling measure.

### Low-degree testing

Elad Haramaty, Amir Shpilka and Madhu Sudan, Optimal Testing of Multivariate Polynomials over Small Prime Fields, SIAM Journal on Computing 42 (2013), 536-562.

- https://people.csail.mit.edu/madhu/papers/2011/hss-eccc.pdf
- https://doi.org/10.1137/120879257

Inspected Definition 1.1, Proposition 1.2, Theorems 1.3 and 1.7 and surrounding hypotheses. Affine line/plane testing is established for low-degree finite-field functions. General abelian targets with non-three-torsion and locally reordered progressions are not simply degree-one F_3-valued maps.

### Projective flag maps

Fedor Bogomolov, Marat Rovinsky and Yuri Tschinkel, Homomorphisms of multiplicative groups of fields preserving algebraic dependence, primary author manuscript.

- https://cims.nyu.edu/~tschinke/papers/yuri/17fieldhom/fieldhom21.pdf

Inspected the finite-field flag definition and Section 2, Theorem 6 and its proof, PDF pages 7-10. This is related local-to-global geometric structure. Its projective lines have different size and its hypotheses do not directly prove our affine hyperplane statement. No publication-priority inference is made from this manuscript version.

### Respected quadruples and all nonnegative weights

W. T. Gowers, A new proof of Szemeredi's theorem, Geometric and Functional Analysis 11 (2001), 465-588.

- https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

Inspected Sections 6 and 14, particularly the graph/respected-quadruple interpretation, the product-property definition on page 555 and Lemma 14.2. Universal nonnegative-weight inequalities are explicit there. Its normalization N^(-1)(sum theta)^4 differs from the present ordinary additive energy E_V(theta), so neither respected energy nor all-weight testing is claimed as a new general concept.

### Sparse-domain affine extension

David Conlon and W. T. Gowers, Freiman homomorphisms on sparse random sets.

- https://arxiv.org/abs/1603.01734
- https://www.its.caltech.edu/~dconlon/homomorphisms.pdf

Inspected Theorem 1.2 and its setting: exact Freiman homomorphisms on a random sparse subset of a finite abelian group extend affinely to the ambient group with high probability. Its arbitrary abelian target is relevant context, but its exact sparse-domain preservation condition differs from the full-domain relative energy condition here.

## Historical boundaries

The search covered affine/local characterization, ternary line and plane tests, hyperplane/complement sections, affine colorings and targets, nested flats, flag maps, group-valued differences, Freiman homomorphisms, respected energy and exact rational thresholds. No equivalent combined arbitrary-target energy theorem with the concrete three/six/nine-point certificates was located in the inspected sources. Formula searches are weak evidence and this negative result is not a novelty certificate.

A systematic MathSciNet/zbMATH review, multilingual search and exhaustive citation tracing were not completed. The quantitative testing machinery is cited only with its fixed-finite-target hypotheses. The arbitrary-target and infinite-dimensional statements are proved directly in the manuscript.

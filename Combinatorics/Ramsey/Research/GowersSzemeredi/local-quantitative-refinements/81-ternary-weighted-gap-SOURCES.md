# Sources and provenance for Report 293

## Mathematical provenance

The manuscript contains the analytic spike proof, complete structural plane split, explicit finite integer-lattice lemma, plane equality and separated remainder, all-rank gluing, and exact cut value. The 729-choice lattice lemma is a reproducible computer-assisted finite component. Every real-weight and infinite-dimensional step is proved in the text, not extrapolated from computation.

Report292, Nine-Point Rigidity on Elementary Abelian Three-Groups, prepared for Vladimir Reshetnikov, 7 October 2026, supplies the preceding derivative reductions, sharp indicator cutoff, gluing, and cut-energy specialization. Its geometry, gluing and cut proof are reproduced in Report293 in the required form. The complex quartic and index-three cut-energy argument originate in Report291, The Sharp Weighted Energy Gap and Three-Coset Extremizers, also dated 7 October 2026.

Frozen Report292 TeX SHA-256: cd1ddcfd7fa813d127278d104ccdad7ac7049aaab169783185258bdd211e4167

Report293 newly combines the complete weighted plane upper bound with the centered all-weight spike lower proof. The latter is what upgrades a one-parameter witness to an unrestricted sharpness theorem. The equality result additionally uses the strict nonspike branches, including the 361/729 generic-branch indicator count. The weight-stability corollary is a direct quantitative consequence of the same positive remainders.

Earlier reports are not downloaded or required during replay and have not been changed. Sharpness uniform over ranks and targets is established here by a rank-two order-two spike. The manuscript does not classify higher-rank equality, prove an optimal remainder constant, or claim sharpness for each prescribed target.

## Exact public inventory

1. README.md
2. REPRODUCING.md
3. SOURCES.md
4. Report293.tex
5. build.py
6. companion/__init__.py
7. companion/README.md
8. companion/exact_checks.py
9. companion/lattice_certificate.json
10. tests/test_build.py
11. tests/test_companion.py

The PDF makes twelve public nonmanifest files. MANIFEST.sha256 lists those twelve and does not list itself. The archive therefore has thirteen entries. Compiler logs, build receipts, page images, exploratory numerical results and working review records are excluded.

## Builder and certificate provenance

The builder and its security regression suite are adapted from the frozen Report292 public files by report-identity and archive-basename substitutions, plus adding the lattice certificate to the exact allowlist and updating its regression count. No-follow snapshots, exclusive outputs, resource limits, subprocess isolation, source immutability, normal/optimized mode comparisons, PDF gates and deterministic archive logic are preserved.

The stand-alone mathematical companion reconstructs all finite source configurations and all 729 midpoint choices. The retained certificate has the complete relation generators and checked unimodular transformations. Verification requires only the Python standard library and does not import earlier research helpers, invoke a computer algebra system or execute upstream code. Sparse-polynomial checks are exact identities, not randomized evaluation tests. The manuscript explains which finite calculation is part of the proof and which diagnostics merely corroborate its other steps.

## Primary literature and inspection scope

The comparison below provides context and attribution. These external works are not hidden premises of the sharp weighted theorem. URLs were verified against primary paper, author, DOI or arXiv records on 7 October 2026. No equivalent theorem with the displayed constant was located in this bounded inspection; that is not a novelty or priority certificate.

### W. T. Gowers

A new proof of Szemeredi's theorem, Geometric and Functional Analysis 11 (2001), 465-588.

- https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

Inspected Sections 6 and 14, particularly graph energy, the product-property definition on p.555 and Lemma 14.2. Respected quadruples and all-nonnegative-weight testing have direct precedent. The normalization there is total mass to the fourth power divided by ambient size, rather than ordinary additive energy.

### Matthew Mizell and James Oxley

Matroids Arising From Nested Sequences of Flats In Projective And Affine Geometries, Electronic Journal of Combinatorics 31(2) (2024), P2.48.

- https://doi.org/10.37236/12183
- https://www.math.lsu.edu/~oxley/EJC_Targets.pdf
- https://arxiv.org/abs/2307.02423

Inspected affine-target definitions, Theorem 4 and relevant restriction/rank statements. The finite ternary coloring theorem gives a broader context for the hyperplane-section geometry, without giving an energy threshold. The report explicitly labels its comparison under the stronger plane-section hypothesis as a derived argument.

### Arnab Bhattacharyya, Eldar Fischer, Hamed Hatami, Pooya Hatami and Shachar Lovett

Every locally characterized affine-invariant property is testable, STOC 2013.

- https://arxiv.org/abs/1212.3849
- https://arxiv.org/pdf/1212.3849
- https://doi.org/10.1145/2488608.2488662

Inspected Theorem 1.2 and surrounding definitions and finite-alphabet hypotheses, not the full proof. This is qualitative testing context; it neither determines lambda nor supplies a target-uniform explicit rejection bound.

### David Conlon and W. T. Gowers

Freiman homomorphisms on sparse random sets.

- https://arxiv.org/abs/1603.01734
- https://www.its.caltech.edu/~dconlon/homomorphisms.pdf

Inspected Theorem 1.2 and its exact sparse-domain preservation setting. The arbitrary abelian target is shared with this report, while its random-domain extension problem differs from the deterministic full-domain weighted ratio.

## Limits of the historical comparison

The bounded search covered respected additive energy, hereditary and nonnegative-weight conditions, arbitrary-target Freiman homomorphisms, ternary affine targets, spike quartics, and finite Fourier reflection or centering inequalities. Exact-number and formula searches found no relevant match; their negative results are particularly weak historical evidence.

No systematic MathSciNet or zbMATH review, exhaustive citation tracing, multilingual search, dissertation review or comprehensive unpublished-work search was completed. No first-use claim is made for universal weights, local-to-global affine geometry, or graph energy. No comparison is presented as a Lean formalization or publication-priority result.

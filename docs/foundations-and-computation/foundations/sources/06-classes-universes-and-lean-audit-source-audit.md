# Source audit

Inspection date: September 21, 2026.

## Supplied manuscripts

The article uses these exact uploaded versions. Line numbers below refer to the original LaTeX files, not to line numbers added by retrieval tools.

### P — surcomplex_polynomial_algebra(2).tex

Title: *Surcomplex Polynomial Algebra: Order Geometry, Newton Profiles, and Scale-Resolved Stability*.

Primary foundational locations: lines 203–246 (set-sized workspaces); 313–345 (support and summability); 665–715 (fixed-degree real-closed-field transfer); 1247–1298 (support-local Hensel recursion); 1868–1939 (set-sized rings and polynomial systems); 2210–2251 (dependency and effectiveness boundary).

Bytes: 112766.
SHA-256: `9d2ad437715ab5a31804a2826911e5f9138fa394aa330c3735ea3dfbfe516005`.

### R — surcomplex_research.tex

Title: *Hartogs Coherence, Finite Maps, and Residue Duality over the Surcomplex Numbers*.

Primary foundational locations: lines 140–221 (workspaces and evaluation); 223–252 (positive operators); 254–305 (automatic support and class replacement in Hartogs); 320–465 (fixed-domain division and parameters); 484–536 (finite-free algebras); 556–662 (finite divided differences and actual fibers).

Bytes: 98818.
SHA-256: `9130327331d5635a6e95bb2bb3f972f92f18fe0dbea9889a8d32f121c857c712`.

### A — surcomplex_analysis(3).tex

Title: *Surcomplex Analysis: Infinitesimal Calculus, Hahn-Coherent Holomorphy, and Contour Theory*.

Inspected sections include the class-theoretic conventions, fine-topological degeneracy, arbitrary-series rescaling, support-preserving gluing (including its componentwise convention), affine charts, all-scale polynomial and rational rigidity, and the topology/coherence comparison.

Bytes: 105194.
SHA-256: `e6e2ef4a8b8d920fffa7256490f98aa312023078fec966c33b3f204cb17748f4`.

A separate global-divisors manuscript is mentioned inside P but was not supplied for this task. Its contents are not treated as independently inspected evidence.

## Pinned Lean repository

Repository: `vihdzp/combinatorial-games`.
Commit: `02b4a908ea2ecfefffecb438f691951a814a5264`.
Commit timestamp returned by GitHub: September 19, 2026, 10:25:40 UTC.
Toolchain: `leanprover/lean4:v4.35.0-rc2`.
Mathlib revision in the inspected manifest: `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`.

The bibliography provides clickable pinned source references. The source inspection covered:

- `CombinatorialGames.lean`: umbrella module inventory.
- `CombinatorialGames/Surreal/Basic.lean`: carrier, numeric quotient, comparison, representative interface, and introductory implementation scope.
- `CombinatorialGames/Surreal/Division.lean`: introductory construction plus the numeric inverse congruence and actual `Field Surreal` declaration in the later inspected range.
- `CombinatorialGames/Surreal/HahnSeries/Basic.lean`: small-support Hahn carrier, constructors, field/order structures, coefficients, truncations, and ordinal support indexing, including the file's concluding section.
- `CombinatorialGames/Surreal/Cut.lean`: complementary sections via concept lattices; these are not small Conway option pairs.
- `lean-toolchain` and `lake-manifest.json`: exact versions above.

The field declaration and small-support machinery were observed in source. No complete normal-form ordered-field isomorphism, real-closedness instance, or surcomplex algebraic-closure specialization was verified in those inspected modules. This is a limited observation, not proof of their absence from every module, branch, repository, or later revision.

The repository was not rebuilt. No transitive theorem-axiom audit was executed. Source inspection and compilation are different verification levels.

## Other public source categories

The article's internal bibliography distinguishes:

1. Foundational surreal constructions and normal forms (Conway and Gonshor).
2. Simplicity-hierarchy characterizations and bounded surreal fields, including the van den Dries–Ehrlich erratum.
3. Hahn-field algebraic closure and support calculus.
4. Class theories, class recursion, and weaker set-theory distinctions.
5. Constructive set theory, HoTT, and higher-inductive semantics.
6. Official Lean universe, axiom, and validation documentation and generated Mathlib documentation.
7. The published ITP 2024 Mizar normal-form development.
8. The March 2026 surreal-arithmetic announcement and slides, explicitly treated as work in progress with details still being checked.

Generated documentation and official “latest” pages are moving sources consulted on the inspection date; they are not substitutes for the repository's dependency lock. No source's broad abstract or aspirational comment is treated as an uninspected formal theorem.

## Claims introduced by this article

The smallness obstruction proofs, the local-recursion explanation, the dependency organization, and the implementation recommendations are expository arguments/designs given in the article. The internally all-scale function sum(t^(n^2) z^n) on C((t^Q)) is supplied with its support proof as a comparison example. No priority claim or machine-verification claim is made for that example.

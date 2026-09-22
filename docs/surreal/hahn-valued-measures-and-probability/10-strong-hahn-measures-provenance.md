# Provenance and proof audit

## Scope and date

Research and source inspection: 22 September 2026.
Pinned Surreal repository commit:
`4cf691c7d951e037739d32d9f5c387dcce724f3c`.

The mathematical statements concern set-sized ordered abelian groups and
countably separated set-sized measurable spaces. Surreal/surcomplex
versions use ordinary normal-form localization of set-sized data.

## Repository material actually inspected

- Root overview (`README.md`), including the Hahn summability and
  formalization descriptions.
- `docs/README.md`, with the 26-report catalog and its distinctions between
  strong summability and topological convergence.
- `docs` and `docs/new` directory inventories at the pinned snapshot.
- A relevant prior `surreal_physics.pdf` text, section 13.3, observing that
  infinitely many equal infinitesimal weights are not strongly Hahn summable.
  That prior observation is credited and is not claimed new.

The GitHub connector code search for "Kolmogorov" returned no matches.
A separate API search returned `incomplete_results: true`. Neither is an
exhaustive proof of absence. The report catalog is not itself a full reading
of every maintained article.

The `docs/new` tree was complete as a directory listing, with 18 entries:

```
hahn_tate_uniformization.zip
surcomplex_exact_and_drifting_multipliers.zip
surcomplex_exact_jet_image.zip
surcomplex_hahn_hilbert_spectral_theory.zip
surcomplex_infinite_spectral.zip
surcomplex_interpolation_research.zip
surcomplex_regular_singular.zip
surcomplex_single_loss_article.zip
surcomplex_tate_uniformization.zip
surreal_autonomous_dynamics.zip
surreal_exponential_automorphism_rigidity.zip
surreal_exponential_rigidity.zip
surreal_holonomic_rigidity(1).zip
surreal_holonomic_rigidity.zip
surreal_localization_bundles.zip
surreal_symbolic_dynamics.zip
surreal_tail_span_research.zip
surreal_theta_research.zip
```

The archive interiors were not fully retrievable. No assertion is made that
the exact results are absent from those unread interiors. In particular,
the contents of `surreal_symbolic_dynamics.zip` were not inferred from its
name or from another dynamics manuscript. An exhaustive repository-priority
comparison remains unavailable in this session.

## Primary literature comparison

The article bibliography contains exact identifiers and links.

1. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*,
   Cambridge University Press, 1986. Used as standard normal-form background;
   publisher bibliographic records were checked, not the entire book.
2. B. H. Neumann, "On ordered division rings," *Transactions AMS* 66 (1949),
   202–252, DOI 10.1090/S0002-9947-1949-0032593-5. The positive-support
   Neumann lemma is an explicit imported theorem, not re-proved or claimed new.
3. Benci–Horsten–Wenmackers, "Non-Archimedean Probability," arXiv:1106.1524,
   journal DOI 10.1007/s00032-012-0191-x, *Milan J. Math.* 81 (2013), 121–151.
   Axiom page inspected as a PDF image (preprint printed page 8). Their
   homomorphism/generalized-limit continuity is not the strong Hahn axiom.
4. Ludkovsky–Khrennikov, "Stochastic processes on non-Archimedean spaces with
   values in non-Archimedean fields," arXiv:math/0110305 (2001). Measure
   definition and extension theorem inspected in text and page images
   (printed pages 3 and 13). These concern a covering ring, ultrametric
   boundedness/continuity, and a measure-dependent completion.

Searches for Hahn-valued probability, strong Hahn additivity, and finite
support/width non-Archimedean Kolmogorov extension did not locate the exact
statements proposed here. Several broad searches returned mostly irrelevant
results, so no exhaustive negative literature claim follows.

## Delicate proof points reviewed

- Coefficient measures are not assumed positive. The scalar atomicity proof
  uses the sigma-ideal of hereditarily null sets, not a false inference from
  leading-coefficient positivity to positivity of all coefficients.
- A countably separated space makes every countable subset measurable.
  This enables the simultaneous-selection argument proving global support.
- The selection argument also proves the stronger coefficientwise criterion
  without assuming strong additivity beforehand. For an already strong
  measure a simpler countable-singleton witness also detects bad support.
- Active widths are monotone even for signed coefficients: a nonzero parent
  must have a nonzero child. Eventual equality forces unique continuation
  and excludes newly born nonzero children under zero parents.
- Positive cylinder values do not imply positive singleton values in
  general. The theorem records the separate point-weight test, and the
  support-order dichotomy identifies precisely when positivity transfers
  uniformly for a prescribed well-ordered set of allowed exponents.
- Infinite product support estimates retain individual outcome labels.
  Testing only aggregate positive probabilities loses information through
  cancellation of higher Hahn coefficients.
- First-error probabilities are recovered by a triangular geometric
  expansion. The front label distinguishes the coordinate/outcome and is
  essential to the coefficient-local-finiteness argument.
- Finite residue-random coordinates are separated before applying
  positive-order product expansions; infinitely repeated constant terms
  are never declared strongly summable.
- Exponent enlargement does not create hidden new coefficient measures:
  every new coefficient would be finitely atomic and zero on every
  cylinder, hence zero everywhere.
- All surreal examples use increasing Hahn exponents mapped to decreasing
  normal-form exponents with a minus sign. Rank two is embedded by
  `(a,b) -> a*omega + b`.

## Verification boundary

The proofs are mathematical arguments, not Lean-checked artifacts or an
independent peer review. The standard-library Python program passed 5,135
exact finite assertions. It cannot establish support well ordering,
countable additivity, or eventual boundedness from finite data. The PDF was
compiled and rendered for visual inspection; typography checking is not
proof checking.

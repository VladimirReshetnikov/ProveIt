# Repository audit

Audit capture: 2026-08-30 13:47:01 PDT

Scope: the materialized worktree during source repair, including the active
merge contents; this is a dated worktree snapshot, not a commit identifier.

## Deterministic TeX inventory

The inventory read every regular `*.tex` file recursively below
`Analysis/FabiusFunction/docs`, sorted by repository-relative path.

- TeX files: **143**
- Newline-counted source lines: **314,509**
- Source bytes: **13,882,029**
- Path-and-content SHA-256:
  `34c73db4cbfbf7eb1441241933e2a4dfd259b387caf2c0a9100eee66d35c567b`

The digest stream is, for each sorted file, its path relative to
`Analysis/FabiusFunction/docs`, a NUL byte, the raw file bytes, and a final
NUL byte. This makes path changes and content changes visible. Counts and the
digest describe the worktree at audit time; later source repairs require a
new dated audit rather than silently reusing these values.

## Method and limits

All TeX bytes were read for the inventory and aggregate digest. The overlap
review then used targeted source searches and direct inspection of the
current primary exposition, frontier compilations, representation synthesis,
and relevant Lean modules. It was not a line-by-line semantic comparison of
all 143 TeX files, a Lean build, or an external literature search. Lexical or
declaration-level overlap can refute a blanket novelty claim, but it cannot by
itself prove that two mathematical statements are equivalent.

Current documentary anchors include:

- `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
- `docs/semi-formalized-research-frontiers/drafts/frontier-compilations/Frontier_Compilations/Frontier_Compilations.tex`
- `docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/Up_Polynomial_Synthesis.tex`
- `docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Inverse_Endpoint_All_Orders/Inverse_Endpoint_All_Orders.tex`

## Overlap register

| Report cluster | Current-corpus overlap | Audit conclusion |
| --- | --- | --- |
| Dyadic zero multiplicity, spectral zeta, and digit sums | The primary/frontier expositions and `DyadicZeroMultiplicity.lean`, `IntegerZeroAnalyticOrder.lean`, and `SpectralZetaWeighted.lean` cover directly related arithmetic, analytic-order, and weighted-zeta layers. | Substantial overlap; no package-wide novelty claim is supportable. |
| Log-periodic endpoint corrections and Lambert saddles | The primary exposition and frontier compilation contain lower-Lambert and periodic-correction sections; related formal work is spread across `PeriodicCorrection.lean`, `FabiusLambert*.lean`, and `NegativeLaplace*.lean`. | Treat the report as a synthesis unless an exact statement crosswalk shows a remaining gap. |
| Appell/Strang--Fix reproduction and first defects | `Up_Polynomial_Synthesis.tex` and the frontier compilation explicitly develop Appell synthesis and sharp reproduction order; related Lean modules include `CompositeMeshSharpness.lean`, `PolynomialCombExactness.lean`, and `RvachevQBinomialFilter.lean`. | Direct topical and result-level overlap; standalone novelty is not established. |
| Generalized or weighted sinc products | The frontier corpus contains integer-base/generalized discussions; `GeneralizedRvachevEntire.lean`, `GeneralizedZeroDivisor.lean`, and `GeneralizedSincZeta.lean` formalize nearby weighted/generalized constructions, not automatically the report's exact base-`b` normalization. | Related formal infrastructure exists; exact equivalence remains to be checked claim by claim. |

## Paper-versus-Lean boundary

The report supplies manuscript proofs, numerical checks, and conjectures. It
does not supply an exhaustive map from each theorem's hypotheses and
conclusion to a named Lean declaration. The module names above identify
related formal infrastructure only. Until a theorem-by-theorem crosswalk is
written and checked, every result in this package remains manuscript/frontier
material rather than a claim of project-level Lean verification.

No global literature-priority conclusion was attempted. The defensible value
of this package is its coherent presentation and reproducible diagnostics;
novelty, if any, must be established for individual claims against both the
current repository and the external literature.

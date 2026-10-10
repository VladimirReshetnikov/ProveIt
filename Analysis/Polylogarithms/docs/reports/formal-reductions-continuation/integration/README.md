# Proposed integration into ProveIt

Baseline commit: `a2a4cf58c49c745058c40e4a6748d472a3420f18`.

No repository files were changed. The following artifacts are ready for review and integration into `Analysis/Polylogarithms`.

## Small independent patch

`editorial_corrections.patch` contains only:

- the logical wording change “Equivalently” → “Consequently” and “The equivalence” → “This implication” around `signed:conj:rank`;
- removal of the duplicated “in the endpoint signs” in the proof of `half:zero:first`.

It passed `git apply --check` against the pinned source. Run the same check against the intended current branch before applying it:

```sh
git apply --check /path/to/editorial_corrections.patch
git apply /path/to/editorial_corrections.patch
```

The patch preserves the conjecture environment. Promote that conjecture to a theorem only when the proof below is included.

## Mathematical insertions

| Destination | Packaged TeX source | Result and dependency |
| --- | --- | --- |
| `chapters/05-signed-kernels.tex`, after the rank conjecture | `article/sections/gaussian_rank.tex` | Proves both absolute rank formulas, all even-weight ranks, canonical kernel, and same-point completeness. Reuses the exact removed-coordinate convention. |
| Following the new Gaussian rank proof | `article/sections/universal_lift.tex` | Universal same-point splitting. The level-three corollary credits the earlier incoming residual invariant ring. |
| `chapters/09-herglotz.tex`, after the formal symbol framework | `article/sections/herglotz_classification.tex` | Complete classification of rational `J` arguments. Depends on the six existing source facts listed below. |
| Following the companion classification | `article/sections/herglotz_rank.tex` | Exact denominator-obstruction rank and all coefficient relations. |
| Following those structural results or beside the rational evaluations | `article/sections/herglotz_identities.tex` | Consecutive log-sine family and explicit values. Credits the known Radchenko–Zagier and Choie–Kumar functional equations. |
| `chapters/09-zero-geometry.tex`, near the elementary-endpoint discussion | `article/sections/lerch_zeros.tex` | Small-parameter classification, initial-velocity counterexample, full `n=2` theorem, and figure. |
| Following the `n=2` theorem | `article/sections/lerch_shape.tex` | Strict decrease of the larger branch and the unique level-one crossing of the smaller branch. |
| Following the Lerch deformation discussion | `article/sections/lerch_abel.tex` | Exact singular Abel coefficient and endpoint regularity of simple zero branches. |
| After `signed:thm:zero-asymptotic` | `article/sections/angular_expansion.tex` and `article/sections/angular_divergence.tex` | Complete expansion and divergence theorem; update the old open-status paragraph together with these proofs. |

`article/sections/lerch_background.tex` restates established framework and supplies short proofs for the standalone article. Within the repository it can be replaced by references to the existing Laplace representation, Appell polynomial theorem, variation bound, and persistence theorem, avoiding duplication.

The source files are `\section` fragments. Adapt heading levels and theorem numbering to the manuscript's book layout. New mathematical labels use `fg:`, `jnew:`, `lerchboundary:`, `lerchshape:`, and `angular:`; preserve or rename them consistently.

## Herglotz dependencies already proved in the source

| Existing label | Required input |
| --- | --- |
| `hstruct:eq:delta-xi` | The invariant cyclotomic boundary, including its rational wedge term |
| `hstruct:thm:kernel` | The exact inversion-symmetric kernel of all-conductor beta symbols |
| `hstruct:lem:positive-Gram` | Positive definiteness of the all-root Gram matrix |
| `hstruct:eq:skew-image` | Its skew-matrix image of a beta symbol |
| `hstruct:lem:norm` | Normalized norms on exterior factors and conductor separation |
| `hstruct:eq:bloch-facts` | Invariant rationalized Bloch descent and the rational boundary map |

The new proper-subfield theorem does not assume injectivity of the logarithmic exterior map on an entire exterior square. It concerns an individual symbol; combinations can behave differently.

## Status updates and attribution

- The full Gaussian ranks are new here. The residual spaces after the same-point family is set to zero were proved in `polylogarithms_research_2026-10-10.zip`.
- The `S4` identity is already proved in `polylogarithms_rigidity_20261010.zip`. Preserve the earlier restricted-system obstruction with its scope, and update any stale global open-status wording.
- The adjacent-argument Herglotz functional lemma is a known reformulation of Choie–Kumar, Theorem 3.2(1), not a new general functional equation.
- The source's `n=1` monotonicity theorem and eventual uniform saturation theorem remain valid. The new results supply higher-index counterexamples, the sharp threshold `K_2=1`, and precise endpoint regularity.
- The complete angular series is proved divergent, including after grouping equal rational bases. Do not describe its ordinary convergence as an unresolved question.
- The unique stationary point of the smaller `n=2,k=1` branch is explicitly conjectural. Only existence of a minimum, the unique crossing of 1, and increasing motion after that crossing are proved.

## Code and supporting files

Keep the verification programs and their corresponding receipts together in an appropriate report or verification directory. `code/run_checks.py` reproduces all theorem-supporting finite checks. The copied upstream Stieltjes routine should retain its provenance and exact content. The zero-branch figure is vector PDF, with PNG and source CSV/JSON supplied.

The full article contains 15 proposed research topics. `CLAIMS.json` separates proved results, antecedents, and the new conjecture. `provenance/` records the exact inspected snapshot and archive blobs.

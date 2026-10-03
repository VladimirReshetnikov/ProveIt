# Provenance and audit boundary

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `20301601562cf84173f2b503b0dc9c3fbf21cd0c`  
Commit timestamp reported by GitHub: 2026-09-29T18:03:55Z.

Directly inspected pinned sources:

1. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Transseries_And_Inversion/README.md`
2. `Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean`

Editorial note (ProveIt, 2026-09-29): both paths are as they were at the
pinned commit. Since the repository split the first file is at
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`;
the second is unchanged at its path. The predecessor below is now filed as
`Analysis/Transseries/docs/series-and-transseries/Support_Controlled_Reversion_One_Exponential/reversion_and_one_exponential.tex`.

The first records statement-level formalization distinctions. The second
provides the finite Catalan/quadratic coefficient core and explicitly identifies
statements it does not formalize. We have not run the repository's Lean build.

An attempt to fetch the large canonical `transseries_and_inversion.tex` through
the repository connector failed because the contents were too large or
unsupported. No full-volume audit is claimed. Search results used for navigation
sometimes pointed to the parent commit; the two direct source reads above were
pinned to the stated commit.

## Directly inspected predecessor

Title: *Support-Controlled Reversion and the Exact One-Exponential Substitution
Group*. Supplied research manuscript dated 29 September 2026.

Filename: `reversion_and_one_exponential.tex`, retrieved from the user's saved
Library, together with relevant indexed material from its PDF.

Inspected passages include the exact mixed-inverse equation, rational
coefficient operator, first three sector functions, deepest-pole formula,
real-positive analytic sector bound, and proposed research questions.
Research question 11.8 explicitly asks for a uniform critical transition and
actual nearby branch points. It is the main project-local target here.

The predecessor is not represented as peer-reviewed literature. This package
contains only the new article and its verification artifacts, not a copy of
the predecessor or repository sources.

## External primary literature

- R. M. Corless et al., *On the Lambert W Function*, Advances in Computational
  Mathematics 5 (1996), 329–359. DOI: 10.1007/BF02124750.
  Author/institution-hosted text inspected, including the branch-point expansion:
  https://uwspace.uwaterloo.ca/bitstreams/384c7b88-c4d1-4401-a363-f1509f8196bd/download
- P. Flajolet and A. Odlyzko, *Singularity analysis of generating functions*,
  SIAM Journal on Discrete Mathematics 3(2) (1990), 216–240.
  https://algo.inria.fr/flajolet/Publications/FlOd90b.pdf
  The exact binomial/gamma coefficient formula and its asymptotics on p. 219
  were inspected, including a rendered page.
- G. A. Edgar, *Transseries for beginners*, arXiv:0801.4877v5;
  Real Analysis Exchange 35 (2010), 253–310.
  https://arxiv.org/abs/0801.4877v5
  Bibliographic record and overview used for general orientation.

No exhaustive literature or worldwide priority claim is made.

## Verification status

The article's new claims have ordinary mathematical proofs in the manuscript.
There is no new Lean proof, interval arithmetic certificate, or independent
referee report. Exact symbolic checks and numerical diagnostics were run
successfully. The final PDF was rendered and visually inspected.

# Source and claim audit

Date of inspection: 29 September 2026.

## Repository evidence actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned transseries README commit:
`ae28ea2db3c01a0b777cffa6295b8fe9c4628f27`

Paths relative to that commit:

- Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/README.md
- Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Transseries_And_Inversion/README.md

Current repository README and selected directory trees were also inspected.
The old group path is not asserted to remain the canonical current path.
The full large canonical transseries TEX source could not be retrieved through
the available endpoint. No exhaustive current-repository nonduplication audit,
current open-status certification, or source-to-render parity claim is made.
The pinned README is used for the research program and formalization boundary,
not as proof of the new mathematical theorems.

(Editorial note, ProveIt, 2026-09-29: those are pre-split paths of the pinned
commit. At the current repository state the two READMEs are
`Analysis/Transseries/docs/series-and-transseries/README.md` and
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`.)

## Earlier user research source actually read

`uniform_q_multinomial_transseries.tex`, saved version dated 29 September 2026,
1,521 source lines. Especially:

- definitions of F_h, T_K, W and the q-multinomial interpolation;
- exact remainder labels eq:Rexact, eq:Rzero, eq:discrete-remainder;
- thm:resonance and the endpoint discussion;
- further-research Question 1 (lattice-to-integral transition) and Question 2
  (first resolved beyond-all-orders correction);
- the slope and inverse-certificate proof.

This is a preceding unrefereed research draft, not asserted to be an established
published theorem or a file verified to be in the present repository snapshot.
The exact positive remainder and conditioning are rederived in the new article.

(Editorial note, ProveIt, 2026-09-29: that draft is now filed at
`Analysis/Transseries/docs/series-and-transseries/Uniform_q_Multinomial_Certified_Inversion/uniform_q_multinomial_transseries.tex`
(batch 45 of `docs/incoming/README.md`). As delivered it had 1,521 lines and
the labels `eq:Rexact`, `eq:Rzero`, `eq:discrete-remainder` and
`thm:resonance` named above. The two drafts checked at scope level below
correspond, by name and subject, to the filed packages
`../Uniform_Resurgent_Crossover_Gaussian_Binomials/` and
`../Support_Controlled_Reversion_One_Exponential/`; the saved copies were not
compared with the filed files.)

The saved drafts `reversion_and_one_exponential.tex` and
`ProveIt_Uniform_Resurgent_Crossover.tex` were checked at scope/abstract level
for overlap. Their principal results are not relabeled as new in this article.

## Public primary/reference sources

- NIST DLMF 4.36, partial fractions of coth.
- NIST DLMF 5.9, Binet and polygamma integral representations.
- NIST DLMF 5.18, q-gamma definitions and limits.
- NIST DLMF 20.7(viii), theta transformations.
- Hughes, Helton, Schlosser, arXiv:2509.16420v1: discrete Laplace methods.
- Costin, Garoufalidis, arXiv:math/0703641: resurgence of Euler–Maclaurin.
- Garoufalidis, Kashaev, arXiv:2008.12465: quantum-dilogarithm resurgence.

The literature check supplies context and citations, not an exhaustive proof
of publication priority. The Gaussian, convexity, and kernel tools have clear
classical precedents. The specialized theorem package is the contribution
advanced for independent expert review.

## Exact status

Conventional analytic proofs are supplied for the stated theorems. No Lean
implementation has been compiled. No interval arithmetic was performed.
The executed Python diagnostics are supplementary. No general resurgent
completion, arbitrary complex-sector theorem, growing-pole-count theorem,
or complete resonance boundary layer is claimed.

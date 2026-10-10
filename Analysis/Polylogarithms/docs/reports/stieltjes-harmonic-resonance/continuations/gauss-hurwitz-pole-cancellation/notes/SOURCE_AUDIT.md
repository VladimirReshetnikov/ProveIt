# Source audit and provenance

## Repository scope

Requested directories:

- `Analysis/Polylogarithms/docs/manuscript`
- `docs/incoming`

The repository was read through the GitHub connector on 10 October 2026. It changed during the investigation. Initial unpinned `main` reads and a later observed HEAD are not represented as one immutable checkout.

Latest observed HEAD: `e0d9463bdee9685dfb1dddb819059cc738540c57` (commit message “New research reports”, reported commit time 2026-10-10T21:44:12Z). That commit added an incoming continuation archive. Its presence was observed; its contents were not audited.

## Inspected canonical material

1. Manuscript `README.md`, blob `02774c39a68fff3792105aed3e2df11e3e604484`: reported S4 proved, S6 and revised S8 conjectural; proof/evidence distinctions.
2. `polylogarithms.tex`: inspected preface and chapter dependencies (initial unpinned read; no immutable blob identifier recorded here).
3. `chapters/07-integration.tex`: Hurwitz integration and Stieltjes material, including the log-gamma integral and existing denominator-five correction. Later, lines 35–55 were re-read at the exact HEAD above. The pinned blob is `52c8487a618429fb8a0cd3978705614b9a193505`.
4. `chapters/04-S4-proof.tex`, blob `7ed3a5f375c027cc87a9c90d9f50e35ca447f1d2`: convergent octahedral involution plus finite rational relation certificate. This is existing work, not reproved here.
5. Targeted repository search results on the already proved odd-index S_(2m+1) family, distribution ranks, and prior harmonic/Gamma reflection results were used to avoid repeating those directions.

The large chapter responses were partly truncated by the connector display. Claims in this package about their contents are restricted to the visible inspected passages; no exhaustive chapter audit is claimed. The optional patch uses the small, complete pinned line-range response rather than a truncated full-chapter response.

## Inspected prior continuation packages

The following archives were available as Library files, copied into the working environment, and their LaTeX sources inspected:

- `ProveIt_Shifted_Hurwitz_Jets_2026-10-10.zip`
- `ProveIt_Stieltjes_Convolution_2026-10-10.zip`
- `ProveIt_Stieltjes_Correlation_Closure_2026-10-10.zip`

They already develop shifted/circular Stieltjes correlations, finite-part/contact-term distinctions, and primitive ladders. The present continuation changes the starting point to Gauss gamma-ratio coefficients. The prior archives are not included in the delivery.

Other incoming archive names were observed, but their contents were not exhaustively inspected. In particular, no statement of novelty relative to every current incoming package is warranted.

## Verified wording correction

At the pinned commit, canonical `chapters/07-integration.tex` lines 43–44 say that basis atoms “must be Q-independent” in a discussion of PSLQ. That is too strong as an algorithmic requirement. Known dependencies should instead be removed or explicitly modeled so that a target-free dependency is not mistaken for a target evaluation. The patch preserves the historical numerical report and changes only that inference.

Earlier continuation work already contains related cautions. This is a scoped editorial correction, not claimed as a new mathematical discovery.

## External primary/reference sources

- NIST DLMF §§15.4, 5.11, 25.11, 25.14.
- W. Bühring, *Partial sums of hypergeometric series of unit argument*, Proceedings AMS 132 (2004), 407–415; arXiv:math/0311126. The HTML full text, including the zero/negative integer-excess statements, was inspected. There is substantive classical overlap at zeroth order.
- O. Espinosa and V. H. Moll, *On some integrals involving the Hurwitz zeta function: part 2*, arXiv:math/0107082, for the integrated Hurwitz-zeta context.
- H. R. P. Ferguson, D. H. Bailey and S. Arno, *Analysis of PSLQ, an integer relation finding algorithm*, Mathematics of Computation 68 (1999), 351–369, DOI 10.1090/S0025-5718-99-00995-3.

Bibliographic URLs appear in `references.tex`. The main identities have full proofs in the delivered article and do not depend on an uninspected conjectural statement in those sources.

## Scope exclusions

No claim of a new proof of S4, a proof of S6/S8, full historical priority, transcendence, linear independence, minimal depth, interval-certified numerical residuals, or proof-assistant formalization is made. No repository write was performed.

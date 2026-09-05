# Source and literature audit

## Supplied repository

The atlas was inspected through the GitHub connector on 4 September 2026:

https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Atlas_and_Frontiers

Retrieved main TeX blob: `7be75f3bc86f9c6712eec6d7550eaea53716434a`.
The document itself is headed as consolidated 28 August 2026. That internal
historical date is not represented as the date of a current repository commit.

Relevant existing material includes the binary product, convolution identities,
finite forward autocorrelation recurrences, Riesz products, and Fabius-related
extrapolation. The present article studies finite **diffraction measures**, not
Fabius spline densities. Targeted inspection found no Stern-named section in the
retrieved atlas. This observation is not a proof that every related identity is
absent from every document or revision in the repository.

## Primary literature used

1. Baake and Grimm (2008), singular-continuous Thue–Morse diffraction and finite
   Fourier recurrences: https://arxiv.org/abs/0809.0580
   DOI: 10.1088/1751-8113/41/42/422001.
2. Klavžar, Milutinović, and Petr (2007), Stern polynomials:
   DOI: 10.1016/j.aam.2006.01.003.
3. Zaks, Pikovsky, and Kurths (1997), the correlation dimension:
   https://link.springer.com/article/10.1007/BF02732440
4. Mauduit, Montgomery, and Rivat (2018), even moments:
   https://link.springer.com/article/10.1007/s11854-018-0050-y
5. Coons, Mazáč, Pincus–Kazmar, and Stout, the explicit dyadic square-correlation
   formula and recent correlation work: https://arxiv.org/html/2511.06386v1
   DOI: 10.1080/10586458.2025.2602541.
6. Baake and Coons (2024), correlation background:
   https://arxiv.org/abs/2209.07102
   DOI: 10.1016/j.indag.2023.02.001.

The open Baake–Grimm manuscript and the open Coons–Mazáč–Pincus–Kazmar–Stout
manuscript were inspected for the specific recurrences and square sums.
Publisher metadata/abstracts supported the historical references for Stern
polynomials, even moments, and correlation dimension. All identities needed by
the new argument are proved again in the article; access to subscription-only
proofs was not assumed.

## Novelty scope

Targeted searches combined Thue–Morse, finite autocorrelation, Stern polynomials,
boundary correction, Riesz products, extrapolation, and Sobolev convergence.
The article treats its exact finite-size connection and the resulting family of
correction and convergence theorems as candidate-new contributions, not as
priority-certified discoveries. In particular, the eigenvalue 1+sqrt(17), the
correlation dimension, the Stern family, and the basic finite Fourier recurrences
are explicitly **not** claimed as new.

## Verification and presentation

The verification run was performed in the working environment using Python's
integer and rational arithmetic. Figures were generated separately using
high-precision arithmetic and ordinary plotting libraries. The article was
compiled with pdfLaTeX via latexmk and visually reviewed from rasterized pages.
The source is self-contained apart from its included table and figure files.

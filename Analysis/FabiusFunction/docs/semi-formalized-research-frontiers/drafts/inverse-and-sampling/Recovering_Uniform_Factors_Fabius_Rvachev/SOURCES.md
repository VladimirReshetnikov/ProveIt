# Sources and provenance

## Repository inspected

Vladimir Reshetnikov / ProveIt:
https://github.com/VladimirReshetnikov/ProveIt

Observed snapshot reference:
`74f7f5bdba1aa728b340509701a0fa4e45e8dbf3`

The review used the GitHub connector for repository metadata and documentation.
The Fabius project overview was read, including its discussion of infinite
uniform convolutions, moment products, the Rvachev up-function, and its Arias
de Reyna source papers:

https://github.com/VladimirReshetnikov/ProveIt/blob/74f7f5bdba1aa728b340509701a0fa4e45e8dbf3/Analysis/FabiusFunction/README.md

The repository root, research-report index and manifest, and Fabius documentation
listings were also consulted for orientation and to avoid treating unrefereed
reports as formal proofs. This was not a complete content or proof audit. In
particular, listing the large Fabius synthesis does not imply that all of its
source text was read.

## Primary mathematical literature

1. Sara C. Billey and Joshua P. Swanson, *The metric space of limit laws for
   q-hook formulas*. Combinatorial Theory 2(2), 2022.
   DOI: 10.5070/C62257868.
   The numbering used in the article is from arXiv:2010.12701v2 (2023):
   https://arxiv.org/abs/2010.12701v2
   Lemma 3.11 gives characteristic functions and cumulants; Theorem 3.13 gives
   identifiability; Theorem 1.15 gives a homeomorphic compact parametrization
   of the appropriate Gaussian-augmented standardized family.

2. Juan Arias de Reyna, *An infinitely differentiable function with compact
   support: Definition and properties*, arXiv:1702.05442 (2017):
   https://arxiv.org/abs/1702.05442
   An English translation of the author's 1982 paper. Used for the conventional
   identification and background of the Rvachev up-density.

3. Juan Arias de Reyna, *Arithmetic of the Fabius function*, arXiv:1702.06487v3:
   https://arxiv.org/abs/1702.06487
   Repository context; no arithmetic theorem from this paper is needed for
   the new Fourier instability construction.

4. Daniel Gerth, Bernd Hofmann, Christopher Hofmann, and Stefan Kindermann,
   *The Hausdorff Moment Problem in the light of ill-posedness of type I*,
   arXiv:2104.06029v2 (2021):
   https://arxiv.org/abs/2104.06029v2
   Related moment-inversion context. It is not used as a substitute for a
   proof that the constructed spectra are positive uniform-factor spectra,
   or for the total-variation estimate of their full laws.

## Novelty boundary

The literature checks identified prior full-law uniqueness and qualitative
parametrization results, so those are explicitly credited. The article's
proposed contribution is the Chebyshev construction, its explicit Fourier
certificate, localization near the Fabius law with fixed variance and uniform
smoothness, and the resulting quantitative inverse/statistical lower bounds.
No exhaustive priority determination was made. No claim is made that a named
published open problem has been resolved.

All literature copies remain external. The package redistributes neither
source papers nor the ProveIt codebase.

# Source attribution and provenance

## Published enumeration source

Andrew R. Conway, Miles Conway, Andrew Elvey Price and Anthony J. Guttmann,
“Pattern-Avoiding Ascent Sequences of Length 3,” Electronic Journal of
Combinatorics 29(4), P4.25 (2022).

- DOI: https://doi.org/10.37236/11266
- Primary preprint: https://arxiv.org/abs/2111.01279
- Sections 2.2 and 2.6 supply the compacted recurrence and bijective justification
- Section 5 supplies numerical analysis of the conjectured factorial exponential constant, not a proof of the present ratio theorem
- Sequence identifiers: https://oeis.org/A202058 and https://oeis.org/A294220

## Preceding research report

“Logarithmic square growth for ascent sequences avoiding 000,” dated
2 October 2026, is the preceding research report. It is not presented as
an independently published external theorem. The PDF and source included
under `prior/` are unchanged from that report's verified distribution.

SHA-256 fingerprints:

- Preceding distribution ZIP: `02ca4fddf80d2fea26afc9958f537477f22de7d54c0c23417e86662b24321baa`
- Included preceding PDF: `51e3d035a41ecf6a6c937190c03930aaad29ff3049ebb7903e9ae47c323f779d`
- Included preceding TeX: `20fd0a9a6969d151067d9758f0fc6720f3a81b4196758800be8e063a1810bd1b`

Imported source locations, using the predecessor's own section numbering:

- Section 3.3, `eq:coarseuniform`: state-uniform characteristic comparison
- Section 10.1, `eq:growing`: large-seed continuation estimate
- Section 10.1, `eq:chernoff`: tilted-length concentration
- Section 10.1, `eq:coarseenclosure`: previous all-index enclosure and root limit
- Section 9, `eq:quantcum`: quantitative cumulative logarithmic-square theorem

The sequel derives the coarse characteristic and Chernoff estimates again.
Its main improved enclosure can therefore be read without the predecessor's
more delicate sharp real-axis analysis. The prior cumulative theorem is
used only for context and the sufficient routes to the still-open full
pointwise logarithmic-square assertion.

## Exact computation

The two frozen root arrays have the identical SHA-256 fingerprint
`ca96899f14eafb143c13401da92e26f75299cee67ebe3f7d6581c853ae93dc8a`.
The precise finite domain and test counts are in `results/finite-scope.json`.
`SHA256SUMS` records every delivered source and data fingerprint. No
floating-point diagnostic is used to certify the exact integer checks or
any asymptotic conclusion.

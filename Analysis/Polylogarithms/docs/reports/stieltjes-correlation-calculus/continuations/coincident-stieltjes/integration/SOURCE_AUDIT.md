# Source audit and correction scope

## Inspected mathematical antecedents

The canonical manuscript README records S4 as proved and S6 and the revised S8 as conjectural. The shifted-Hurwitz continuation already proves separated Stieltjes closure, derivative contact corrections, and normalized primitive/log-Gamma correlations. The classical same-point Hurwitz product kernel appears in Espinosa–Moll (2002, preprint 2000). None of these is claimed as a newly discovered formula here.

Selected parts of `shifted-hurwitz-jets/sections.tex` were inspected at the pinned revision, including the explicit further-research collision question. The new result is scoped to that question's function-level collision expansion and finite-constant comparison. The additional delta-supported distributional comparison remains open in this package.

## A precise safeguard, not a fabricated source error

For total derivative order `r=p+q>0`, the coordinate Hadamard moment differs from the raw spectral Laurent constant by

    r! zeta(r+1) [(-1)^q H_p + (-1)^p H_q].

For `p=q=1`, omitting this correction gives

    6 zeta(3) + 4 zeta'(3)

instead of

    2 zeta(3) + 4 zeta'(3).

The reason is that the entire parameter-dependent resonant endpoint monomial must be removed, not just its pole residue. This warning prevents an incorrect extension of the classical spectral formula. The inspected earlier report did not assert the wrong same-point value and explicitly excluded a same-point construction. Accordingly, no allegation of an existing false theorem is made.

## Limits

Only selected relevant source portions were read. The five binary ZIPs in the incoming inventory were not accessible for content inspection, so no claims about their theorems, correctness, overlap, or priority are made. The canonical manuscript was not audited page by page. GitHub search results were used as navigation leads rather than treated as an exhaustive current index.

Global literature priority, independent peer review, interval certification, and proof-assistant formalization have not been established. The article proves its all-index results analytically, with computational checks explicitly separated.

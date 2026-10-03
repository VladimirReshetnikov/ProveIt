# Source specific attribution review

Review date: 2 October 2026

## Finding

The revised abstract, historical-attribution subsection, bibliography, README, and change note appropriately credit the substantive overlap with Prellberg's 2002 work. No further attribution change is required. The revised report makes no priority claim for the leading formula, parabolic-coordinate method, or displayed correction coefficients. It distinguishes a historical announcement from the self-contained proof and certificate supplied in this package.

This is a source-specific attribution and preservation review. It is not a new independent proof of the complete asymptotic theorem, a proof-assistant certification, or an exhaustive priority search.

## Sources and exact locators

1. Thomas Prellberg, *On the asymptotic analysis of a class of linear recurrences*, FPSAC 2002 slides. [Primary PDF](https://webspace.maths.qmul.ac.uk/t.prellberg/talks/recurrence.pdf)
   - Numbered slide 12, physical PDF page 37: individual coefficient definition before summing over depth
   - Numbered slides 14–15, physical PDF pages 43–48: conjugacy to a shift and log-polynomial inverse-iteration expansions
   - Numbered slide 17, physical PDF pages 55–59: pre-sum asymptotic; its final complete display is on physical page 59
   - Numbered slide 26, physical PDF pages 92–97: further terms computed by a different, non-rigorous method; this statement does not identify the present report's particular correction coefficients

2. Marni Mishna's summary of Prellberg's seminar of 23 September 2002, in *Algorithms Seminar 2002–2004*, edited by F. Chyzak, INRIA (2005), printed pages 47–50. [Primary seminar summary](https://algo.inria.fr/seminars/summary/Prellberg2002a.pdf)
   - Section 2.1, printed page 48, equation (3): the coefficient X(n,m)
   - Section 2.2, printed page 49, equation (6): inverse-coordinate expansion
   - Section 2.2, printed page 49, unnumbered display after equation (7): the individual-coefficient asymptotic before the depth sum
   - Printed page 50, Theorem 1: the broader summed statement, which is not used as a black-box proof in the revised report

The relevant source displays were checked from the PDFs, including visual inspection of printed page 49 and the slide-17 build. PDF-page numbers above are one-based and differ from numbered slide labels because animation builds occupy separate pages.

## Exact specialization and its significance

In the source notation take f(z)=exp(z)−1, c=1/2, d=1/6, b(z)=z, and a(z)=a₀ with 0<a₀<1. Here H(n,m) means n! times the coefficient of zⁿ in the m-fold compositional iterate of f; it is not an ordinary m-th power.

The defining coefficient identity is X(n,m)=a₀ᵐH(n,m)/n!, and the homogeneous solution can be normalized by Y(μ(s))=a₀ˢ. In the pre-sum formula, Y(μ(m)) contributes a₀ᵐ, while the a₀ˢ inside the integral cancels its reciprocal. Since 1−d/c²=1/3, the resulting displayed shape is

H(n,m)/n! ∼ 2^(−n) m^(n−1−n/(3m)) J(n/m),

where J(β) is the historical contour integral of μ(s)exp(βs)/(2πi). This matches the specialization printed in the revised report.

At m=n, multiplication by Stirling's formula gives the leading n^(2n−5/6)/(2ⁿeⁿ) scale. With m=n+k and fixed k, the same leading form gives the factor eᵏ, provided the contour amplitude is interpreted consistently near β=1. This algebraic match establishes material historical overlap; it does not import missing uniform-error estimates from the brief sources.

The report correctly avoids asserting an unconditional equality of its fixed-radius amplitude with the historical contour integral: contour orientation, continuation, and additive-coordinate normalization must first be matched. Its own amplitude definition and certificate remain the basis of its theorem.

## Scope of the general-theorem caveat

The stated limitation of the broad printed theorem was checked against the earlier Takeuchi report and directly by substitution. With f(z)=z/(1−z), a(z)=z, b(z)=1, and the ordinary Bell series B satisfying B(z)=1+f(z)B(f(z)), the series X(z)=1+zB(z) satisfies X(z)=a(z)X(f(z))+b(z). Its nth coefficient is B(n−1), rather than a nonzero constant multiple of the printed B(n) scale.

This supports the warning that the broad statement requires an additional restriction or normalization. It does not remove the pre-sum formula or parabolic method from the historical record. The revised report preserves that distinction and labels its equation (32) as a historical announcement, not an imported proof. It also expressly avoids treating the OEIS conjecture labels as evidence of novelty.

## Preservation checks

Compared directly with the original frozen report package:

- The TeX body from “Result and exact model” through the end of the inverse section is byte-identical
- inverse-section.tex is byte-identical
- All five files under verification/ are byte-identical
- All nine files under results/ are byte-identical
- All three files under source/ are byte-identical

The only changes in the main TeX source are the abstract, historical discussion and related literature wording, bibliography, and bibliography label width. The original mathematical result, finite-contour argument, remainder construction, amplitude enclosure, code, numerical records, and inverse mathematics are unchanged. The new historical comparison is explanatory material, explicitly outside the proof's dependency chain.

The rebuilt PDF was checked by text extraction and visual inspection of the changed pages: page 1 and pages 10–12. The new attribution text, formula, and references are present and readable, with no clipping or overlap observed on those pages. This limited visual check is not a claim to have repeated the original full-document layout review or mathematical replay.

## Frozen identities

The following SHA256 values were independently recomputed after the final source freeze was confirmed. Paths are relative to the revised package root.

- iterated-bell.tex: 6126e2c0b3d9d81312058f2128a1786a077b040c8c837a6d3edcefc3f7f0b41b
- iterated-bell.pdf: 75f866386ccd0e15d1849f20c0d7f42e0116900f5baf1dde0372b21db24a4ca1
- README.md: 8dda1e97fc60bcebe834e9fdf7ba08282cd4833824d74b0ae616a9d0f8bd6a44
- CHANGE-NOTE.md: 8097ce9f6dcbd00fff0539c3e2ddb37786c82fc341926c045cef4990394ce7e8


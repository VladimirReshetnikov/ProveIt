# Source provenance and claim boundary

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit:

    23dd71d2d3d5e85d2b97a8cc45f55e735d69a4ae

Principal source:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/
    representations/common_digit_fabius_zonoids_frontier_report/
    common_digit_fabius_zonoids.tex

The line breaks above are only for readability; they form a single path.
The fetched blob SHA was `b605248e7c100a17414974d9407e954abb43c4f0`.

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/blob/23dd71d2d3d5e85d2b97a8cc45f55e735d69a4ae/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/common_digit_fabius_zonoids_frontier_report/common_digit_fabius_zonoids.tex

## Relevant source content

The inspected report already supplies the common-digit construction and the
joint sinc product (`thm:joint-char`). Its `thm:density-regularity` proves
smooth compactly supported density and qualitative boundary flatness using
nonsingular Vandermonde blocks. These are baseline facts, not novel claims here.

Its subsection “Sharp ray-wise decay of the joint sinc product,” with label
`conj:ray-decay`, proposes a quadratic logarithmic envelope governed by the
largest surviving parameter. It additionally suggests a periodic or
quasiperiodic remainder depending on arithmetic relations between parameter
logarithms. The present article proves the leading envelope in a precise
window/relative-measure formulation and extends it to moving logarithmic
boxes. It does not prove the proposed finer remainder description.

The present article then derives the full mixed Lp derivative law, the
minimum-rate matrix conjugacy, the signed resonance, and the stated
consequences. Its signed extension requires distinct parameter moduli until
the separate opposite-parameter factorization is invoked.

The source README also records a separate 2026 correction and continuation
for polynomial-geometric jet small deviations. The present boundary-flatness
upper bound is not a replacement for that work, and is not a matching
small-deviation or endpoint-mass expansion.

## Classical primary references checked

J. Fabius, “A probabilistic example of a nowhere analytic C-infinity-function,”
Zeitschrift fuer Wahrscheinlichkeitstheorie und Verwandte Gebiete 5 (1966),
173–174. Institutional preprint record (1965):
https://ir.cwi.nl/pub/8160

J. Arias de Reyna, “An infinitely differentiable function with compact support:
Definition and properties,” arXiv:1702.05442 (2017), an English translation of
the author's 1982 article:
https://arxiv.org/abs/1702.05442

The scalar dyadic derivative-norm identity is credited to the explicit
up-function derivative formula in the latter reference. It is only a
normalization check, not a new theorem of this package.

## Limits of the comparison

Repository overview/index material and the specifically relevant report,
README, and theorem/conjecture passages were inspected, supplemented by
focused searches and retrieved related research context. The minimum-rate
mixed-derivative formula was not located in that inspected material. This
is a bounded comparison, not a complete audit of every repository file or
all prior literature. No absolute priority or “world-first” claim is made.

The repository was read, not modified. No theorem in this package obtains
Lean-formal status merely by continuing the ProveIt project. No Lean/Rocq
proof or kernel-check receipt is supplied.

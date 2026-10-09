# Pinned source and literature audit

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pin: `13d60da8e683ca02b11c6b301c068bda929014e7`.

The repository was read through the available GitHub connector. This was a focused
source inspection, not a local full checkout, a complete native code audit, or a
native timing baseline. No repository writes were made.

Files under `Topology/UnknotRecognition/` inspected for this continuation:

| Path | Inspected material and use |
|---|---|
| `README.md` | Full fetched overview; historical checkpoints are not relabelled as our test results |
| `synthesis/report.tex` | Introductory lines 1–200: algorithmic target, hierarchy accounting, distinction between scalar invariants and recognition |
| `synthesis/README.md` | Fetched early and later integration ranges (1–330 and 650–950); identifies already-integrated rank-two terminal and later forest/word developments |
| `synthesis/primitive_projection.tex` | Full fetched section; source-provenance rule, simultaneous primitive-pair quotient, raw grammar bound |
| `synthesis/primitive_forest.tex` | Full fetched section; unit-coordinate forest, cycle exclusion, native scope and overhead caveats |
| `synthesis/group_certificates.tex` | Lines 1–90; full-group endpoint, source-reconstructed presentation, Tietze elimination |
| `reports/45/README.md` | Full fetched report overview; compressed primitive-power scope and existing arithmetic work |

The first root/overview reads were through `main`; source search then supplied the
pin above, and the substantive projection/forest/report-45/group reads were made at
that pin. Early directory/tree listings were navigational and are not a content
inventory of the entire repository. A code search returning no match for a keyword
is not used as evidence of novelty. The top-level README includes older checkpoints;
later synthesis content takes precedence when describing integrated functionality.

## Primary literature

- Himeno, Motegi, Teragaito, *Generalized torsion, unique root property and
  Baumslag–Solitar relation for knot groups*, arXiv:2208.00621v1, 2022;
  Hiroshima Mathematical Journal 53 (2023), 345–358. Lemma 2.3 is the balancedness
  input. The PDF pages containing the lemma/proof and examples were visually read.
  https://arxiv.org/abs/2208.00621
- Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
  arXiv:2607.23350v1, 2026. Section 9 and Proposition 9.1 distinguish the iteration
  count from operation-cost estimates. The pertinent PDF page was visually read.
  https://arxiv.org/abs/2607.23350
- Gemein, *Representations of the singular braid monoid and group invariants of
  singular knots*, Topology and its Applications 114 (2001), 117–140. The classical
  statements used are Theorem 1.1 and Definition 3.1. Source construction is checked
  independently in the delivered code rather than treating conventions as implicit.
  https://www.maths.ed.ac.uk/~v1ranick/papers/gemein.pdf
- Kronheimer–Mrowka, *Khovanov homology is an unknot-detector*, Publications
  Mathématiques de l’IHÉS 113 (2011), 97–208, arXiv:1005.4346. Used only for the
  independent small-cube rank criterion, not for a new complexity bound.
  https://arxiv.org/abs/1005.4346
- Bar-Natan, *Fast Khovanov homology computations*, Journal of Knot Theory and Its
  Ramifications 16 (2007), 243–255, arXiv:math/0606318. Attribution for the maintained
  scanning method; the shipped oracle is deliberately a full small cube instead.
  https://arxiv.org/abs/math/0606318
- Papakyriakopoulos, *On Dehn’s lemma and the asphericity of knots*, Annals of
  Mathematics (2) 66 (1957), 1–26. Foundational attribution for the cyclic-group
  endpoint; the explicit Loop-Theorem argument was also read in the pinned native
  group-certificate section and is reproduced as a proof in the new article.

External bibliographic information was checked during this request. The literature
search is not exhaustive; no claim of global priority or external peer review is made.
No third-party paper or source archive is redistributed in this package.

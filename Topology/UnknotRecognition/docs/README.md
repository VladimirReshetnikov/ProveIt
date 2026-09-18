# docs

Source material shared by all six attempts and by the synthesis.

* `quasipolynomial-talk.pdf`: Marc Lackenby, *Unknot recognition in
  quasi-polynomial time*, February 2021, 109 PDF pages including
  progressive-reveal duplicates. Page references in the archives' reports and
  in `../synthesis/report.pdf` are physical page numbers of this file.

Map of the talk (physical pages):

| Pages | Content |
|---|---|
| 11–14 | the theorem: `n^O(log n)` for an `n`-crossing diagram |
| 15–30 | hierarchies, boundary patterns, essential patterns, essential hierarchies as certificates of knottedness |
| 38–53 | simplifying an inessential hierarchy with a violating disc; the basic algorithm as a flowchart |
| 54–65 | termination by a lexicographic complexity; the `L g^L` estimate |
| 66–74 | the four speed-ups: quadratic surface complexity, compressed encodings, multi-surfaces, Heegaard splittings and Cheeger regions |
| 75–108 | sketches of each speed-up, the Cheeger condition with factor 1/3 |
| 109 | the final flowchart naming BUILD HIERARCHICAL MULTI-SURFACE, CUT ALONG SURFACE, USE CHEEGER REGION, HAKEN'S LEMMA, WEAKLY REDUCE, SIMPLIFY MULTI-SURFACE |

* `arXiv-2607.23350v1/`: the arXiv source and PDF of the related preprint,
  Marc Lackenby, *Incompressible surfaces, hierarchies and unknot
  recognition*, 25 July 2026, 54 pages (`algorithm-incompressible-250726.tex`,
  `algorithm-incompressible-250726.pdf`, the arXiv PDF renamed to match its source, figures). Section 9, "The number of steps", is the part
  that matters for the running-time question: it gives the iteration bound
  `L(g+1)^L` and states that the steps are not specified precisely enough for
  a running-time estimate and that `g` and `L` are not bounded there.
  Proposition 2.6 (patterns on a ball) and Definition 3.4 (pattern
  complexity) are used by the archives. A plain-text extraction of the PDF is
  in `../synthesis/data/lackenby2026-extracted-text.txt`.

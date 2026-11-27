# Merged article

[`article.pdf`](article.pdf) merges the 131 research reports under
[`../Research`](../Research/) into one article of 723 pages, *Beyond the Riemann hypothesis
for Dirichlet L-functions: consequences, transfers and limits*. Each result is stated once,
in the strongest form the reports prove. A result that follows from a stronger or more
general result of the collection, with hypotheses no stronger, is left out, and so is
repeated material: the reports' many accounts of the upstream Lean proof are replaced by
one section.

The article is a merge, not a review. Its mathematics is that of the reports. Nothing was
recomputed, and the claims have not been independently checked or formalized. The input
theorem, RH and GRH for Dirichlet L-functions as stated in the external Lean development
`lsernau/grh-lean`, is taken as given. Every result carries one of three marks:
*unconditional*, *uses Dirichlet GRH*, or *reduction; the target estimate is open*. No
result of the last kind proves a new Riemann hypothesis or any named conjecture.

## Files

- `article.tex` is the main file. It inputs `preamble.tex`, the abstract and introduction,
  and one file per section under [`sections/`](sections/). The bibliography is
  `references.bib`, merged from the per-section files under [`bib/`](bib/).
- [`provenance/`](provenance/README.md) has one table per section. It lists, for every
  section of every report, where its material went, and for every omitted result the result
  that supersedes it.
- To rebuild, run in a scratch copy of this directory: `pdflatex article`, `bibtex article`,
  then `pdflatex article` twice. The build needs only standard LaTeX packages.

## Sections

| Part | Section | File | Results | Unconditional | Uses GRH | Reductions |
|---|---|---|---:|---:|---:|---:|
| I | The source theorem and its transferable mechanism | [`src.tex`](sections/src.tex) | 10 | 9 | 1 | 1 |
| I | One-sided analytic criteria | [`ana.tex`](sections/ana.tex) | 78 | 54 | 16 | 0 |
| I | Li coefficients, moment pencils and positivity certificates | [`li.tex`](sections/li.tex) | 41 | 21 | 20 | 0 |
| II | Nonabelian zero detection: general reductions | [`nab.tex`](sections/nab.tex) | 41 | 24 | 10 | 10 |
| II | Detectors for specific Galois groups and fields | [`grp.tex`](sections/grp.tex) | 45 | 28 | 1 | 17 |
| II | Degree-two targets: Artin, Hecke and modular L-functions | [`hec.tex`](sections/hec.tex) | 39 | 20 | 3 | 14 |
| III | Zeros, Euler products and prime races under Dirichlet GRH | [`zer.tex`](sections/zer.tex) | 87 | 19 | 66 | 1 |
| III | Recovering zeros and characters from prime data | [`rec.tex`](sections/rec.tex) | 141 | 68 | 83 | 0 |
| III | Direct arithmetic consequences of Dirichlet GRH | [`dir.tex`](sections/dir.tex) | 82 | 37 | 51 | 0 |
| III | Imaginary quadratic fields of class-group exponent six and seven | [`cls.tex`](sections/cls.tex) | 13 | 7 | 6 | 0 |
| III | Sparse equations for singular moduli | [`smd.tex`](sections/smd.tex) | 32 | 16 | 2 | 0 |
| IV | Progression-free sets in polynomial rings and finite rings; additive constraints | [`gpp.tex`](sections/gpp.tex) | 34 | 34 | 0 | 0 |
| IV | Progression-free sets of integers and of ideals | [`gpi.tex`](sections/gpi.tex) | 28 | 22 | 0 | 0 |
| IV | Graph towers, spanning-tree valuations and signed cycles | [`gra.tex`](sections/gra.tex) | 30 | 24 | 0 | 0 |
| V | Torsion specialization: selection theorems | [`tors.tex`](sections/tors.tex) | 28 | 16 | 0 | 0 |
| V | Torsion specialization: exact costs, obstructions and coefficient fields | [`cost.tex`](sections/cost.tex) | 31 | 25 | 0 | 0 |
| V | Lubin–Tate branches, jet recovery and Fleck congruences | [`lub.tex`](sections/lub.tex) | 34 | 30 | 0 | 0 |
| VI | The Selmer, Galois-cohomology and K-theory interface | [`sel.tex`](sections/sel.tex) | 44 | 39 | 0 | 0 |
| VI | Spanning, frames, auxiliary characters and matrix statistics | [`spn.tex`](sections/spn.tex) | 76 | 72 | 1 | 0 |
| | Total | | 914 | 565 | 260 | 43 |

"Results" counts theorems, propositions, corollaries and lemmas. The status columns count
the marks in theorem headings; lemmas and corollaries are often unmarked, so the status
columns do not add up to the first.

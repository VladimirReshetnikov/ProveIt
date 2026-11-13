# iPRA: the verified frontier and a fixed-type obstruction

**The requested new axiomatization below the current complexity frontier was not obtained.**
This archive is a research report with a precisely scoped negative result and
reproducible comparison evidence. It is not labeled as a solved minimization problem.

The report is `ipra_frontier_church.pdf`; its standalone LaTeX source is
`ipra_frontier_church.tex`. Read the first page and `STATUS.json` for the exact
claim boundary.

## Results

1. Independently remeasured eight complete incumbent Python programs under
   CPython 3.12.14. The compact observed coordinate envelope is 239 tokens /
   256 AST nodes / 461 normalized bytes, from different programs and interfaces.
   The strict native Eq/D envelope is 317 / 356 / 597, also from different
   programs. Deterministic maximum-compression gzip sizes are recorded for
   every program.
2. Proved a three-element model theorem for a specific pure, simply typed,
   fixed Church-number arithmetic. The model admits every closed typed numeric
   operation, coverage, zero separation, and even full formula induction.
   It cannot support an ordinary finite-dimensional interpretation of iPRA,
   including definable subdomains, finite parameters, and definable quotients.
3. Gave a separate finite-set proof of the known impossibility of a uniform
   predecessor at any fixed simple Church type. This is not a claim about all
   combinator encodings, polymorphism, new arithmetic constants, or new sorts.

The failure of bi-interpretability does **not** establish failure of
equiconsistency. The report makes no new checker record or historical novelty claim.

## Reproduce

```sh
python3 reproduce.py
python3 code/measure.py
python3 code/verify_church_obstruction.py
```

The first command verifies the manifest and all finite evidence. The measurement
script parses but does not execute the archived proof checkers. Use Python 3.12.14
for the recorded normalization. Compression library versions are in the receipt.
Run the verification scripts without `-O` or `-OO`.

An additional syntax search in `code/search_three_cycle.py` independently
reproduces the existing nine-node scalar three-cycle bound. It is explicitly
an archived failed reduction experiment, not a new mathematical contribution.

## Build the PDF

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_frontier_church.tex
```

Requires standard pdfLaTeX packages listed in the source. The copied foundation
chapter fragments are references, not dependencies of the report build.
Alternatively, `python3 build_pdf.py` handles an installed TeX distribution
without a format cache by building a private format; it downloads nothing.

## Sources and scope

The initial repository pin was `798856e4ef2d02b7f9c0f1660828c5ce58f277f2`.
The final pin is `c0c9ef353e9ac3c877c9c5cb37354e1721baada4`; the change integrated
the five inspected incoming packages without changing the earlier incumbent
artifact subtrees or the Chapter 1 / Chapter 11 foundation files.
`PROVENANCE.json` records exact original paths, hashes and commit pins.

`reference/checkers/` contains eight exact upstream source files and gzip-9
copies of their normalized source, not newly devised proof checkers.
`reference/foundation/` contains the inherited bridge and checker-accounting
chapters. These reference materials retain the ProveIt MIT No Attribution
license in `reference/LICENSE-ProveIt.txt`.

The new mathematical claims were independently reviewed in writing. No new
Lean/Rocq formalization is included and the upstream Lean project was not rebuilt.
Finite tests establish their displayed calculations, not the quantified
metatheorems about all typed lambda terms.

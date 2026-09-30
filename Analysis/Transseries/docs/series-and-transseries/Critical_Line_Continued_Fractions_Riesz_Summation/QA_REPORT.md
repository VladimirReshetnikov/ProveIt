# Quality assurance and verification record

## Final document

- Title: **At the Critical Line: Continued fractions and sharp Riesz summation
  of resonant transseries**.
- 23 A4 PDF pages, including title page, contents, and references.
- Compiled from the supplied source with pdfTeX 1.40.26 in three passes.
- Final log: no LaTeX warnings, undefined references, multiply defined labels,
  duplicate destinations, overfull boxes, or underfull boxes.
- All table inputs and bibliography entries are included in the package.
- No external source documents, private working notes, or font files are included.

## Rendering and inspection

Every final PDF page was rendered with PyMuPDF 1.26.7 and inspected in two
contact sheets. The title, critical-line classification, Riesz theorem, and
numerical tables were also inspected at readable resolution during production.
The final Riesz-theorem page was independently rendered and inspected with
Poppler (`pdftoppm`). No clipping, overlap, or broken mathematical glyphs was
observed. A text-geometry scan found no spans outside the physical page, no
replacement glyphs, and no unresolved `??` reference markers.

The PDF is searchable and includes a linked table of contents and references.
It is not a tagged accessibility PDF; no PDF/UA conformance is claimed.

## Executed mathematics diagnostics

`verify.py` passed 192 exact finite assertions and 49 numerical assertions at
110 decimal digits. Recorded environment:

- Python 3.13.5
- SymPy 1.14.0
- mpmath 1.3.0

The numerical tests are not directed-rounding interval certificates. The
infinite continued-fraction constructions, the infinite tail estimates, and
the inverse theorem are established by the written proofs, not by these
finite diagnostics.

Two additional manual API guard checks confirmed rejection of literal
coincident-pole inputs with periods `(1, 1)` and `(1, 3/2)`. These checks are
not included in the 192/49 mathematical assertion counts. The implementation
also rejects gaps that become indistinguishable from a collision at the
current precision; it does not implement general confluent residues.

Running `build.sh` regenerated all six data files under `build/results/`.
Each agreed byte for byte with its recorded counterpart under `results/`
in the recorded environment. The recorded data were not overwritten by
that build.

## Mathematical scope reviewed during preparation

The report explicitly distinguishes:

- increasing-action convergence from separate-lattice convergence;
- the logarithmic exponent from Sondow's irrationality base;
- uniform collision bounds from continuity at a collision on the cutoff;
- sharp period-uniform smoothing order from fixed-input minimal order;
- simple weighted residues from weights placed inside multiple-pole residues;
- analyticity of the block sum from convergence of its raw derivative series;
- a local inverse estimate from global univalence or full inverse resurgence.

The source comparison is pinned to the stated repository commit and target
question. This is not an independent peer review, a global priority audit,
or a Lean formalization.

## Clean archive smoke test

The 15-file ZIP was extracted into a fresh working directory and `build.sh`
was executed there. All 192 exact and 49 numerical checks passed again. The
rebuilt PDF had the same 23-page count and identical extracted text as the
delivered PDF; the six regenerated result files matched the recorded files
byte for byte. PDF binary identity is not promised because build timestamps
and document identifiers can change.

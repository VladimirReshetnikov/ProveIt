HOLDER AND ZYGMUND SPECTRA OF THE RVACHEV--THUE--MORSE OPERATOR
================================================================

Finite Fourier reduction, critical Jordan chains, and optimal decay
Research manuscript prepared for Vladimir Reshetnikov
October 2026

TOPIC AND PROVED SCOPE

The article develops the spectral theory of the Rvachev--Thue--Morse
transfer operator on periodic Holder--Zygmund spaces of every positive
order, including the corresponding little spaces. It also treats every
nonnegative finite trigonometric Markov mask with integer dilation b>=2.

The general method gives an exact contraction after quotienting by a
finite Fourier core. The core matrix determines exterior spectral values
and their generalized eigenspaces. The article proves the full Fredholm
essential disk, the point spectrum, the big/little boundary Jordan
classification, and exact residual operator-power orders.

For the repository normalization L=P/2, the periodic spectrum at order
s>0 is the closed disk of radius 2^(-s-1), together with 1/2 and -1/4.
At order s=1, the big Zygmund space has two nontrivial Jordan chains of
length two at -1/4; the little Zygmund and classical C^1 spaces retain
only the two-dimensional ordinary eigenspace there. Both Zygmund spaces
have residual operator norm of exact order n*4^(-n) at this threshold.

For the Rvachev operator, the noninteger Holder results extend to [0,1],
and the critical classical C^1 generalized eigenspace is identified there
as well. The integer interval-Zygmund problem is not claimed as solved:
the article explains why matching finitely many endpoint derivatives
does not suffice. Sharp local classical C^1 resolvent growth, weighted
endpoints, infinite Fourier tails, and other extensions remain proposed
research questions. The arbitrary finite-mask results are periodic.

The source questions come from the Fabius-function branch of ProveIt.
The earlier integer C^r result, normalization, elementary three-mode
eigenfunctions, and endpoint-jet algebra are explicitly credited.
The new arguments relative to that baseline are identified in the
article and in provenance.json. No claim of worldwide priority or
global novelty is made.

FILES

holder_zygmund_spectra.tex
    Complete LaTeX manuscript, with its bibliography and TikZ figure.

holder_zygmund_spectra.pdf
    Compiled 22-page article: one unnumbered title page, a roman-numbered
    contents page, and 20 Arabic-numbered content pages.

README.txt
    This guide: scope, requirements, inventory, and reproducibility.

Makefile
    Three-pass PDF build, exact finite verification, and auxiliary cleanup.

provenance.json
    Repository URL, pinned commit, exact baseline path and blob identity,
    retrieval date, starting questions, and inherited/new distinctions.

verification/verify.py
    Reproducible standard-library Python program using exact rational
    and integer arithmetic.

verification/results.json
    Deterministic output of the successful finite verification run.

verification/COMPUTATIONAL_NOTES.txt
    Mathematical conventions, checked identities, example matrices,
    parameter ranges, interpretation, and computational limitations.

verification/VALIDATION_NOTES.txt
    Record of finite verification, independent mathematical review,
    and build-log checks.

verification/PDF_QA.txt
    Separate final rendering and presentation review of all 22 pages,
    including pagination, page destinations, layout, and text bounds.

PDF COMPILATION

Use a conventional TeX installation with the packages declared at the
start of the manuscript. No external graphic files, bibliography database,
BibTeX run, network access, or shell escape are required. The figure is
drawn by TikZ and the bibliography is included in the LaTeX source.

From the package directory, run:

    make build

The build runs the following command three times so the table of contents,
cross-references, and PDF destinations settle:

    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error holder_zygmund_spectra.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error holder_zygmund_spectra.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error holder_zygmund_spectra.tex

EXACT FINITE VERIFICATION

Requirements: Python 3.9 or later, standard library only.

From the package directory, run:

    make verify

Equivalently, from the verification directory, run:

    python3 verify.py --output results.json

The recorded run passed 47,127 exact checks: 21 for the sine core,
22 for the higher-frequency core, 46,752 for the degree identities,
and 332 for defects, the right inverse, and truncated critical series.
All scalar arithmetic is rational or integer. There is no floating-point
eigensolver or symbolic-algebra dependency. Explicit exception-based
checks remain active if Python is run with optimization enabled.

Finite computations verify the displayed matrices, polynomial identities,
ranks, and selected finite instances of the degree formulas. They do not
prove an infinite-dimensional spectral disk, Banach-space membership,
convergence of an infinite series, or exhaustion of generalized
eigenspaces. Those claims rest on the conventional mathematical proofs
in the manuscript. No fresh Lean or Rocq build was run, and no
proof-assistant verification of the new theorems is claimed.

CLEANUP

    make clean

This removes only the manuscript's LaTeX auxiliary files. It retains the
final PDF, LaTeX source, verification program and results, and all notes.

SOURCE SNAPSHOT

Repository:
    https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:
    a21208b3ff14a07a4c8318dbf916d543acbef043

Baseline Git blob:
    45a9a8724aa42f2f6812d39bb486211438dcb09f

Retrieved date:
    2026-10-05

See provenance.json and the article's source-provenance appendix for the
complete path and the exact distinction between reused background and
arguments supplied in this package.

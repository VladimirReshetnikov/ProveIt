MINKOWSKI'S CONVEX-BODY THEOREM IN iPRA
Research package prepared for Vladimir Reshetnikov
14 November 2026

START HERE
==========
Read paper/minkowski_ipra.pdf. Its complete LaTeX source is
paper/minkowski_ipra.tex together with the numbered section files and
references.tex in the same directory.

MATHEMATICAL RESULTS AND SCOPE
=============================
The paper gives a complete human-readable proof of the strict theorem in an
explicit first-order arithmetic representation. Finite rational boxes in
half the lattice-normalized body have disjoint interiors and total content
exceeding 1. Refinement to a common mesh gives more cells than residue classes.
A bounded collision search produces a nonzero integer coefficient vector z;
symmetry and one midpoint put Bz in the body.

The proof includes:
* A uniform primitive recursive extractor and a quantifier-free induction
  audit for the fixed rational matrix/slab/box input format.
* A theorem scheme for any arithmetic membership formula, using canonical
  rational codes, symmetry, midpoint closure, and box-inclusion premises.
  This scheme does not require a decision procedure for arbitrary membership.
* A quantitative reduction from ordinary rational-polytope volume to the box
  certificate, with explicit mesh and search bounds and finite volume lemmas.
* The closed rational-polytope equality case, using a finite integer-facet
  enlargement that preserves the integer points.
* An explicit obstruction for the unrestricted real equality case: its
  rectangle instances imply weak real sign choice / LLPO, and a fixed
  primitive recursive family admits no uniform recursive point selector.

First-order iPRA does not quantify over arbitrary real sets. For represented
real bodies, the strict theorem uses positive inner-volume evidence or a
separately justified procedure providing that evidence. Real basis data must
support the required constructive nonsingularity. The paper states these
representation conditions explicitly; it does not silently import classical
measure theory or unrestricted choice into iPRA.

DIRECTORY INVENTORY
===================
paper/
  Compiled article, complete LaTeX sources, Makefile, and the included figure.
code/
  minkowski.py: exact rational certificate validation, extraction, and
                independent arithmetic/geometric witness verification.
  grid_certificate.py: bounded inner-grid frontend at a supplied mesh and
                       search window; imported by the example generator.
  make_examples.py: regenerate exact example inputs and witnesses.
  test_minkowski.py: nine implementation test methods.
  make_figure.py: optional regeneration of the paper's illustration.
examples/
  Square, skew lattice, diamond, and three-dimensional cube certificates and
  witnesses. rational_equality.json records the additional closed-square
  equality example; it is not an input to the main certificate CLI.
lean/
  Three uncompiled Lean source outlines, seven-milestone README, expanded
  formalization plan, matching toolchain, and pinned source provenance.
verification/
  Recorded Python test and LaTeX build logs. These are implementation/build
  checks, not a completed Lean proof.

RUN THE EXACT PYTHON ARTIFACTS
=============================
Run these commands from this package's root directory. Python 3.12 was used;
the extractor, frontend, example generator, and tests use the standard library.

  python3 code/make_examples.py
  python3 code/test_minkowski.py
  python3 code/minkowski.py examples/diamond.json
  python3 code/minkowski.py examples/diamond.json --verify examples/diamond.witness.json

The first command regenerates the example files. The third prints a newly
extracted witness. The fourth checks the supplied witness without replaying
the collision search. To save an extracted witness to a chosen file, use:

  python3 code/minkowski.py examples/diamond.json --output diamond-recomputed.witness.json

Rational inputs use integers or exact fraction strings; floating-point input
is rejected. The recorded test run passed all nine test methods. Finite tests
support the implementation; the paper supplies the general mathematical proof.

The code implements certificate extraction and a supplied-mesh frontend. It
does not implement the entire arbitrary-polytope volume/triangulation algorithm
proved in the paper. A too-small grid search window can fail to find sufficient
inner volume but cannot certify an invalid volume witness.

REBUILD THE PDF
===============
A LaTeX installation with pdflatex and the standard packages named in the main
source is required. The supplied figure PDF avoids any plotting dependency.
To force a fresh three-pass build from the package root, run:

  make -B -C paper

The output is paper/minkowski_ipra.pdf. Optional figure regeneration requires
Matplotlib and NumPy:

  python3 code/make_figure.py
  make -B -C paper

LEAN STATUS AND REPOSITORY ALIGNMENT
===================================
ProveIt repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected commit: 329161f8da0b319d51ba9f6246c4b19d243f7193
Recorded toolchain: leanprover/lean4:v4.32.0
The pinned root lakefile declares ConciseIPRA and pins Mathlib v4.32.0.

THE LEAN SOURCES ARE UNCOMPILED AND INCOMPLETE.
No Lean or Lake executable was available in the delivery environment. The
files define typed data, targets, short conditional proof scripts, and explicit
remaining obligations. They are not a completed finite-pigeonhole proof, a
completed formal geometry development, or a completed object-level derivation
of type Prf PRAAx [] (...). No new axioms or sorry declarations were inserted
to disguise that missing work. Absence of those strings is not verification.

A host Lean theorem about Nat, Rat, or Real is insufficient by itself for the
claim of iPRA provability. The roadmap explicitly requires the actual
ConciseIPRA object-theory derivation, followed by the repository's translation
to the concise scalar presentation.

See lean/README.txt for build commands within the pinned ProveIt checkout and
seven completion milestones. This package's lean/ directory is not a standalone
Lake project. lean/sources.json records the exact inspected module paths,
content SHAs, and immutable GitHub URLs.

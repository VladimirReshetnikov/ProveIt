CONSTRUCTIVE MORDELL-WEIL DESCENT IN iPRA
=======================================

Date: 2026-11-15

START HERE
----------

Read paper/mordell_weil_ipra.pdf (26 pages). The complete editable LaTeX
source is paper/mordell_weil_ipra.tex and its seven included .tex files.
For the precise formalization boundary and implementation plan, read
Section 7 of the paper and lean/LeanPlan.md.

WHAT IS PROVED
--------------

1. A general primitive recursive finite-descent theorem. A fixed coded
   abelian group with a finite bounded-height enumeration and a proved
   decomposition P = 2 Q + R_i satisfying 2 h(Q) <= h(P) + C has an
   explicit finite generating list and primitive recursive coordinates.
   Descent takes at most bitlength(max(h(P)-C,0)) active steps. The paper
   gives the coefficient bounds and quantifier-free state invariants.
   A compact-word version needs no group identities.

2. A constructive theorem for every nonsingular integral elliptic model
   E: y^2 = x^3 + A x + B, RELATIVE TO an actual finite rational list R
   satisfying the covering assertion

       for every P in E(Q), there are i < length(R) and Q in E(Q)
       such that P = 2 Q + R_i.

   The paper derives the needed selector from this assertion; it does
   not assume an effective selector as additional input. It proves
   explicit duplication and translation height bounds, complete rational
   halving by a finite rational-root scan, finite generator enumeration,
   and a total bounded coordinate algorithm under the covering hypothesis.

3. An UNCONDITIONAL arithmetic theorem for E_1: y^2 = x^3 - x, proved by
   a bounded version of Fermat's square-area descent:

       E_1(Q) = {O, (0,0), (1,0), (-1,0)} = (Z/2Z)^2.

   The paper also proves the uniform scaled case
   E_u: y^2 = x^3 - u^4 x for every nonzero rational u, and all finite
   products of these curves. Their rational groups are (Z/2Z)^(2r), with
   explicit point lists, relations, and coordinate maps. These are
   Q-isomorphic scalings and their products, not arbitrary twists.

WHAT IS NOT CLAIMED
-------------------

The package does not prove a uniform generator algorithm for arbitrary
elliptic curves, or an unrestricted constructive Mordell-Weil theorem
for arbitrary abelian varieties over arbitrary number fields. Obtaining
actual rational representatives for the quotient is an explicit remaining
input to the general theorem. Finite Selmer data do not automatically
provide such representatives. The paper cites current official and primary
sources for the general open effectivity problem.

No impossibility or independence theorem about iPRA is asserted.

The written arithmetic proofs are not yet complete deeply embedded Lean
proof objects of type Prf PRAAx. The delivered Lean code checks native
finite-descent and search theorems, a finite group table, and concrete
definitions. The full elliptic arithmetic and E_1 classification targets
in EllipticSpec.lean are named propositions, not asserted axioms or proved
theorems. The paper and LeanPlan specify the remaining proof obligations.

VERIFICATION RESULTS
--------------------

* All six Lean source files compile using Lean 4.32.0, commit
  8c9756b28d64dab099da31a4c09229a9e6a2ef35. They require Std and their
  sibling modules; no mathlib dependency is needed for the delivered code.
* No delivered Lean file contains a sorry proof or a new axiom declaration.
  The principal native descent/search theorems use propext and Quot.sound.
  E1FiniteTable.two_generators uses no axioms. Native Rat in EllipticSpec
  has transitive proof-field dependencies that can include Classical.choice;
  it is an implementation specification, not an iPRA arithmetic proof.
* All 14 Python tests pass (nine elliptic tests and five coordinate tests).
  Arithmetic uses integers and fractions.Fraction, not floating point.
* The duplication resultant is checked coefficientwise in Z[A,B], by
  expanding all 8! permutations. The result is exactly
  256*(4*A^3+27*B^2)^2.
* The PDF was compiled in three passes and visually inspected. The final
  log has no overfull boxes, undefined references, or missing characters.

Tests are implementation checks. They are not a proof that a supplied list
covers a rational group, that a finite point search finds every rational
point without a height bound, or that the full theorem has been formalized.
The complete E_1 point classification follows from the written descent,
not from the regression search to height 256 or 4096.

REPRODUCTION
------------

Run these commands from the extracted package directory. Python 3.10 or
later is sufficient; the Python code uses only the standard library.

    python3 -m unittest discover -s tests -v

To regenerate both detailed JSON verification reports:

    python3 tests/test_elliptic.py
    python3 tests/test_coordinates.py

To print the exact symbolic determinant calculation separately:

    python3 code/symbolic_resultant.py

To compile the Lean sources with the version in lean/lean-toolchain:

    bash lean/build.sh

If Lean is installed at a custom path:

    MW_LEAN_BIN=/absolute/path/to/lean bash lean/build.sh

The script compiles the four library files, runs the axiom audit, and
evaluates the example. Its final numeric outputs are word size 16 and
evaluated value 37. lean/verification.txt preserves the observed output.

To rebuild the PDF with a normal TeX Live/LaTeX installation:

    python3 code/build_pdf.py

Alternatively, from paper/:

    latexmk -pdf -interaction=nonstopmode -halt-on-error mordell_weil_ipra.tex

The source uses standard AMS, Latin Modern, geometry, microtype, booktabs,
longtable, enumitem, listings, xurl, hyperref, and fancyhdr packages.
The optional --local-tex mode in build_pdf.py can construct a private
format when Debian's TeX sources are installed but its format/database
configuration is missing; it was used for the delivered PDF. Shell escape
is disabled. This fallback is not needed in a normal TeX installation.

On systems with sha256sum, verify the delivered files with:

    sha256sum -c SHA256SUMS

Do this before rebuilding, since generated logs and metadata may change.

FILE INVENTORY
--------------

paper/mordell_weil_ipra.pdf    Complete human-readable paper.
paper/mordell_weil_ipra.tex    Master LaTeX source.
paper/01_foundations.tex      Exact scope; iPRA; codes; elementary arithmetic.
paper/02_descent.tex          Generic descent, fuel, coefficients, word form.
paper/03_elliptic.tex         Heights, resultant, halving, conditional theorem.
paper/04_unconditional.tex    Full Fermat descent; E_1; scalings and products.
paper/05_formalization.tex    Lean interfaces and object-theory proof plan.
paper/06_validation.tex       Implementation checks and precise status table.
paper/references.tex          Bibliography and pinned repository references.

lean/DescentCore.lean         Complete native finite-descent word theorem.
lean/FiniteSearch.lean        Complete native finite Boolean search theorem.
lean/E1FiniteTable.lean       Complete four-element group table verification.
lean/EllipticSpec.lean        Concrete codecs, operations, and target Props.
lean/DescentExample.lean      Executable natural-number descent instance.
lean/Audit.lean               Axiom dependencies and target type checks.
lean/LeanPlan.md              Detailed dependency-ordered implementation plan.
lean/lean-toolchain           Lean version pin.
lean/build.sh                 Reproducible compilation script.
lean/verification.txt         Compiler, axiom audit, and example output.

code/elliptic.py              Exact curve arithmetic, certificates, halving.
code/coordinates.py           Bounded traces, coefficients, generator lists.
code/symbolic_resultant.py    Exact polynomial determinant expansion.
code/build_pdf.py             Three-pass PDF build and optional TeX fallback.

tests/test_elliptic.py        Nine exact arithmetic tests and report writer.
tests/test_coordinates.py    Five extraction/certificate tests and writer.

metadata/elliptic_checks.json Detailed elliptic arithmetic results.
metadata/coordinate_checks.json
                             Traces, coefficient checks, symbolic resultant.
metadata/mathematical_audit.txt
                             Mathematical scope and independent cross-check.
metadata/repository_audit.txt Inspected upstream definitions and reuse limits.
metadata/source_manifest.json Pinned sources and retrieval information.
metadata/validation_summary.json
                             Concise machine-readable verification status.
metadata/pdf_build.txt        Successful three-pass PDF build output.
SHA256SUMS                   SHA-256 checksum of each other delivered file.
README.txt                   This guide.

REPOSITORY REUSE AND PROVENANCE
------------------------------

Inspected ProveIt revision:
    27da047166883e5010e115968d3a40f9e91bfb3d

Repository:
    https://github.com/VladimirReshetnikov/ProveIt

The ConciseIPRA files define the actual first-order theory and proof
calculus. The existing Diophantine geometry and Faltings packages provide
relevant height, descent, and square-area developments. The present package
spells out the arithmetic and strengthens the general descent interface by
deriving a bounded selector from actual covering representatives.

The repository was inspected read-only at this revision. This package is
independently reproducible; it does not include or require an upstream
checkout merely to compile its native Lean examples. No upstream build or
full repository correctness claim is implied. The source audit gives exact
paths, and the bibliography links to the inspected revision.

The mathematical constructions are standard in origin; no claim of novelty
for Fermat descent, Mordell-Weil height descent, or the four-point group
classification is made. The purpose is to give explicit bounds, witnesses,
logical scope, and a concrete route into the requested weak formal theory.

LOCAL CERTIFICATES FOR DIOPHANTINE CONSISTENCY
Shared Pell orientation and smaller quartics with unit coefficients
Prepared for Vladimir Reshetnikov / ProveIt, 24 October 2026

START HERE

Read report.pdf for the mathematical argument, comparison table, complete
306-variable residual transcription, verification scope, and source identities.
The complete LaTeX source is report.tex together with its adjacent .tex inputs.
All delivered polynomials are fixed ordinary polynomials over unrestricted
integers. There are no implicit positivity restrictions or variable exponents.

For each of the four selected polynomials P, ordinary mathematics formalizable
in ZFC proves

  ZFC |- (there is no integer tuple x with P(x)=0) <-> Con(ZFC).

The new transformations are composed with the identified inherited numerical
C222/ZF/ZFC calibration. This is not a proof of either consistency or
inconsistency. The release does not claim a globally simplest equation, an
end-to-end new proof-assistant certificate, or historical priority for every
ingredient. It does provide literal coefficient files, unbounded mathematical
proofs of the new reductions, and separately implemented finite checkers.

RESULTS

All four equations have total degree four.

  direct306:    306 variables;  6,259 monomials; height 128,446; 206 residuals.
  matched1252: 1,252 variables; 27,738 monomials; height 1; constant 1.
  principal985: 985 variables; 95,609 monomials; height 1; constant 1.
  sparse1122:  1,122 variables; 25,922 monomials; height 1; constant 1.

The direct equation is the sum of the squares of all 206 displayed quadratic
residuals. Relative to the pinned 324-variable parent it removes 18 variables
and two residuals, while adding 451 collected monomials and preserving height.

The unit-coefficient equations have every nonzero coefficient equal to +1 or
-1. They permit individual fourth powers. The matched1252 profile starts from
exactly the same 442-variable source as package127's 2,215-variable,
30,468-term graph equation. Its reduction therefore isolates the new graph
contraction rather than a smaller source. The other two graph profiles also
use the new direct306 source: principal985 favors arity; sparse1122 favors
support. The latter improves both arity and support over the older graph.

The central new arithmetic device is a linear trace-orientation defect in an
existing bounded Pell residue pool. Its residue is nonnegative even though
the actual linear expression need not be. It recovers nine orientations and,
with an explicit noncircular bootstrap and one strict product, replaces nine
separate sign graphs. The graph device replaces a sufficient global C4-free
factor restriction by complete collected-coefficient certification of a
logical alias identification. A four-term nonnegative quartic equality energy
removes some remaining third aliases without changing the zero set.

NORMATIVE EQUATIONS AND FORMAT

  direct/integer306/equation.json
    Ordered variables and all residuals; P is their sum of squares.
  direct/integer306/expanded_polynomial.json
    Complete collected coefficient list for the same polynomial.
  graph/matched1252/polynomial.json
  graph/principal985/polynomial.json
  graph/sparse1122/polynomial.json
    Complete collected coefficient lists, variable metadata, and exact metrics.

An entry [c,[i,j,j]] means c*z_i*z_j^2. The empty index list is the constant
monomial. Indices are zero based. Metadata names impose no domain restrictions
and add no variables. The equation in every case is exactly P=0.
Readable complete transcriptions accompany every selected equation.
EQUATION_IDENTITIES.json records their byte sizes and SHA-256 identities.

OFFLINE VERIFICATION

Requirements: Python 3.10 or later, with its standard library. No network,
external computer algebra system, or proof-assistant installation is required
for the supplied finite checks. From this directory:

  python3 -B verify.py
  python3 -B -O verify.py
  python3 -B verify.py --rebuild

Verification is read-only. The optional rebuild recreates all six direct files
in a temporary directory and eighteen selected graph JSON artifacts in memory,
then compares their exact bytes. It does not overwrite the delivered equations.
An optional --output /absolute/path/receipt.json saves a receipt. Choose a path
outside this directory once its integrity manifest has been sealed.

The direct checker tests 929 explicit conditions and four deliberate corruptions.
A second checker independently verifies the raw power interfaces, all retained
and added rows, all 216 parent restoration polynomials, and every expanded
coefficient. The graph checkers recover the complete sum-of-squares energy,
logical alias classes, units, and flow interfaces, and independently collect
every coefficient. The integrated check also rejects four corrupted graph
artifacts, checks source identities, and parses every printed LaTeX residual
back into exact integer coefficients. Verification/optimization-mode receipts
are in verification/. Those build receipts were recorded before final checksum
sealing; a present run also validates the completed MANIFEST.sha256 inventory.

These finite computations certify exact algebra and artifact correspondence.
They are not a finite test of the unbounded consistency equivalence. The
unbounded arithmetic proofs and the inherited logical calibration are stated
and identified separately in the report.

EVALUATION AND WITNESS LIFTING

For a JSON array of exactly 306 integers:

  python3 -B evaluate.py point.json --equation direct306

The other --equation choices are matched1252, principal985, and sparse1122;
supply the indicated number of integer coordinates. Evaluation is exact.
It does not decide whether any integer zero exists.

The graph component additionally constructs the canonical witness lift from
an arbitrary source tuple, with its exact off-solution energy identity:

  python3 -B graph/evaluate.py source_point.json --profile principal985 \
    --lift --output lifted_point.json

For source residuals R_r this checks

  2*P(L(z)) = sum_r R_r(z)^2 + (sum_r R_r(z))^2.

On source zeros this is the constructive forward witness map. The graph
transformation is a bijection on source zero sets. The direct transformation
preserves existence of integer zeros but need not biject individual tuples,
because its nonnegative-integer representation witnesses are nonunique.

BUILDING THE PAPER

A conventional TeX installation with latexmk, pdfLaTeX, and the packages named
in report.tex suffices. To regenerate the data-derived tables and appendix:

  python3 -B build_report_data.py

To compile:

  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The delivered PDF was rendered and visually inspected on all pages. Its
compilation had no overfull, underfull, or package-warning messages. PDF bytes
may vary with TeX versions and metadata; mathematical coefficient files are
the normative finite artifacts. Rebuilding or editing files can invalidate
the release's byte inventory, as expected.

SOURCE AND INTEGRATION

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned snapshot: 1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61

The direct parent is package131's centered integer324 equation. The matched
graph source is package125's integer442 equation, and the inherited graph
compiler is package127. Packages 127 through 133 and the specified incoming
material were examined rather than relying only on the older main catalogue.
Exact source paths and identities appear in provenance/ROOT_SOURCE_PINS.json,
direct/SOURCE_PINS.json, and graph/SOURCE_PINS.json. Retained Lean interface
files identify the logical calibration; they are reference files, not a
standalone transitive Lean project built by this release.

Keep this directory intact when incorporating it into ProveIt. Internal paths
are relative; no current repository numbering or external directory layout is
assumed. No upstream files were modified or pushed as part of this delivery.

License and attribution are in LICENSE and NOTICE.txt. Independent review in
this packet means separately implemented checks and reasoning within an
AI-assisted workflow; it does not imply external human or formal-kernel review.

A SINGLE NUMERICAL CONSTRUCTOR AND THREE INFERENCE FAMILIES FOR iPRA
Research package prepared for Vladimir Reshetnikov, 12 November 2026

RESULT

This package gives a complete presentation using numerical terms

    t ::= x | 0 | R(n,a;i,u.h)

and formulas s=t or D_(x,y)B. Successor is the abbreviation R(0,a;i,u.0).
Both object-language binding constructors bind two variables in their last
child. The calculus has the fixed reflexivity clause and exactly three
inference families: Use, Introduce, Open with an inferred witness.
Computation is built into full canonical normalization.

The report supplies written proofs of equiconsistency and bi-interpretability
with full first-order intuitionistic primitive recursive arithmetic. Both
numerical domains are whole, equality is actual equality, and both numerical
composite isomorphisms have graph x=y. The arithmetic compiler handles each
fixed finite primitive-recursive description; no universal numerical evaluator
is assumed.

This is a new combination of inherited ingredients, with an exact compatibility
proof and a smaller complete matched implementation. The counter recursor,
decoder, direct recursion macro and short ordinary logical macros are inherited
from uniform_binding. The inferred-opening logical calculus and its main
completeness construction are inherited from inferred_witness. They are fully
credited in the paper.

MEASURED IMPROVEMENT AND LIMITS

Entire standalone module, CPython 3.12.14, ast.unparse plus one LF:

                                      bytes   tokens   AST nodes
    Pinned scalar inferred-opening     1990     683       771
    Fully normalized counter R         1965     683       764

The new checker saves 25 normalized bytes and seven AST nodes with unchanged
token count. It is not the global repository minimum: the repository has
smaller compact and other public-language checker profiles. No absolute
minimality theorem, literature-wide priority claim, or new Lean/Rocq
verification is made. Tests supplement the written mathematical proofs.

START HERE

    report.pdf                 Compiled mathematical report.
    report.tex                 Self-contained LaTeX source.
    code/checker.py            Complete standalone acceptance module.
    code/FORMAT.txt            Full certificate and scoping contract.
    code/examples/             Thirteen accepted proof certificates.
    code/rejection_controls.json
                               Twenty-one targeted negative controls.
    reproduce.py               Compiler, independent evaluators, tests,
                               fixture regeneration and source measurement.
    evidence/verification.json Observed verification results and metrics.
    evidence/provenance.json   Pinned sources, hashes and attribution.
    CLAIMS.json                Machine-readable scope of the claims.
    reference/                 Exact inherited comparison checker, supporting
                               proof constructors, fixtures and proof excerpts.
    SHA256SUMS                 Archive-member checksum manifest.

REPRODUCE

The checker and verification use only Python's standard library.

    python3 reproduce.py
    python3 code/checker.py < code/examples/reflexivity.json

For an induction example that uses its hypothesis:

    python3 code/checker.py < code/examples/used_equation_induction.json

Acceptance is normal exit with exactly ACCEPT followed by a line feed.
Invalid proofs are rejected by an exception/nonzero exit. Ordinary resource
limits are not logical acceptance. The ignored premise payload of an
unconditional clause should be JSON null.

The reproduction program regenerates the positive/negative fixtures and the
verification report. Its proof compiler and generators are untrusted: every
generated proof is inspected by the standalone checker. The recorded finite
checks are detailed in the PDF and JSON evidence.

Compile the PDF with a normal TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The source embeds the complete checker listing and needs no external TeX
fragments. The reference .tex excerpts are archival sources, not standalone
documents or build dependencies.

PROVENANCE

Repository:
    https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:
    9f9545f5ffd9e0392d4a36639503aca12383450a

Project:
    Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All inherited files are under the repository's MIT No Attribution license,
included in reference/LICENSE-upstream.txt. Supporting reference text files
have terminal line feeds normalized; the measured comparison checker retains
its exact pinned bytes and recorded SHA-256. No changes were pushed to the
repository.

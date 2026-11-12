A ONE-BODY CONTEXT CALCULUS FOR iPRA
==================================
Prepared for Vladimir Reshetnikov, November 11, 2026.
Comparison commit: 11814771b7490dfbea0ed5fcf0f5b23586334764
Repository: https://github.com/VladimirReshetnikov/ProveIt
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

RESULT AND LIMITATION
---------------------
This package proves a structural simplification of the existing raw clause
presentation of iPRA. A context stores one formula body B(y), whose reading
is B(0) -> forall y B(y), instead of storing an independent antecedent and
body. Ordinary assumptions are represented by an iterator gate. The object
language and its interpretation are unchanged. Atomic reflexivity, the two
established Eval cases, Use, Open and Intro are the complete rule inventory.

The written proof establishes the exact same open consequence relation and
therefore transfers the established bi-interpretation with full first-order
iPRA. Both numerical domains are whole, equality is actual, and both
numerical composites have graph x=y. The new proof is independently reviewed
written mathematics, not a newly compiled Lean/Rocq formalization.

The new mathematical presentation does NOT beat the established proof-checker
size criterion in the implementation supplied here. Its complete checker is
3130 normalized bytes versus 2999 for a matched control. The gate machinery
costs more than removing the independent context field saves. No global
smallest-axiomatization claim is made.

A SEPARATE implementation improvement of the existing native Eq/D checker
reduces 788 bytes / 358 tokens / 413 AST nodes to 778 / 357 / 412. This is a
strict improvement in all three coordinates, but changes no mathematical
axiom or inference rule. A 777-byte alternative is included; its 415 AST
nodes make it less suitable when all coordinates matter.

PACKAGE CONTENTS
----------------
ipra_one_body.pdf         Complete 12-page paper.
ipra_one_body.tex         LaTeX source of the paper.
build_pdf.py             Portable two-pass LaTeX build helper.
CLAIMS.json              Machine-readable claim and limitation ledger.
MANIFEST.sha256          SHA-256 hashes of the package contents.
verify_manifest.py       Checks the manifest without modifying the package.

code/README.txt          Full checker protocol, test details and provenance.
code/checker_one_body.py Main new mathematical calculus.
code/checker_clausal_control.py
                        Matched two-field context control.
code/checker_native_pareto.py
                        Preferred smaller implementation of the existing
                        full native Eq/D checker, 778 normalized bytes.
code/checker_native_refined.py
                        Byte-priority variant, 777 normalized bytes.
code/checker_native_control.py
                        Exact pinned upstream 788-byte comparison source.
code/reproduce.py        Repeats checker measurements and validation.
code/build_examples.py   Regenerates raw-calculus proof certificates.
code/examples/           Positive and invalid proof certificates.
code/metrics.json        All complete-source size coordinates.
code/results.json        Executed validation results.
code/audit_gate_scopes.py
                        Independent numerical-environment scope test.
code/native_refactor_audit.txt
                        Independent source audit of the native refinement.
code/PROVENANCE.json     Exact inherited paths, commit and source identities.
code/LICENSE-upstream.txt
                        Repository's MIT-0 license for inherited code.

reference/               Unmodified inspected upstream theorem files and
                        README, plus UPSTREAM.json. These are provenance
                        sources, not a self-contained Lean project.

REPRODUCTION
------------
Use CPython 3.12.14 to reproduce the recorded exact size metrics. The
checkers and scripts use only the Python standard library.

From this directory:

    python3 verify_manifest.py
    python3 code/reproduce.py

The reproduction script locates its own directory; no special PYTHONPATH is
needed. It rewrites code/metrics.json and code/results.json with current
measurements and outcomes. Run the manifest check before reproducing because
reproduction may change metadata in those evidence files on another Python
version.

Standalone examples:

    python3 code/checker_one_body.py < code/examples/one_body/induction_uses_assumption.json
    python3 code/checker_one_body.py < code/examples/one_body/nested_d_assumption_extraction.json
    python3 code/checker_native_pareto.py < code/examples/native/computation_successor_local.json

The executed suite passed 140 standalone process checks (ordinary Python
and python -O), 37764 candidate/control validator comparisons from 18882
cases, and 36462 independent gate endpoint/scope checks. Tests supplement
the written proof; they are not a proof of bi-interpretability.

To rebuild the paper, use a standard TeX Live installation containing
pdflatex, Latin Modern, AMS packages, geometry, microtype, booktabs,
hyperref, listings and fancyhdr:

    python3 build_pdf.py

The original PDF was compiled from this source and all 12 pages were rendered
for visual inspection. No repository changes, commits or pull requests were
made as part of this delivery.

RESEARCH DIRECTION
------------------
The next substantive goal is to eliminate the independent context field
without paying for explicit gated-assumption lifting. The paper includes
further research questions and the exact noncircular conversion/access
proof that a formalization or a different checker can reuse.

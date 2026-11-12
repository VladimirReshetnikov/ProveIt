CONCISE iPRA: A MEASURED IMPLEMENTATION REFINEMENT
Prepared 12 November 2026 for Vladimir Reshetnikov

RESULT STATUS
=============
This package does NOT establish a new axiomatization below all three current
complexity coordinates. It establishes a matched byte refinement of an existing
guarded iPRA proof checker, from 516 to 513 normalized bytes. The new program
has 268 significant tokens and 306 AST nodes; the existing separate records
of 256 tokens and 278 nodes are not improved.

The mathematical axiomatization and whole-domain bi-interpretation are
inherited from the pinned ProveIt development. The new contribution is the
implementation transformation, its written trace/completeness argument,
an explicit control-only certificate, and reproducible validation.

START HERE
==========
ipra_frontier_review.pdf  -- compiled 16-page research report (page count may
                             vary with an independently installed TeX system)
ipra_frontier_review.tex  -- complete main LaTeX source
CLAIMS.json              -- machine-readable claim boundaries

CODE AND REPRODUCTION
=====================
code/checker_compact.py   -- measured 513-byte module; assumes the stated
                             integer/list certificate and guarded-goal contract
code/checker_strict.py    -- standalone alphabet and public-grammar validation;
                             measured separately at 1183 normalized bytes
reference/checkers/      -- pinned comparison modules and matched strict control
fixtures/                -- 21 inherited regression cases plus one new
                             certificate accepted only by the controls
reproduce.py             -- standard-library measurements and finite checks
evidence/results.json    -- executed results under CPython 3.12.14
build_pdf.py             -- builds the PDF, generating a temporary TeX format
                             if the installed TeX distribution lacks one
verify_manifest.py       -- verifies SHA-256 checksums in MANIFEST.sha256

Commands from this directory:

    python3 reproduce.py
    python3 code/checker_strict.py < fixtures/computation_zero_local.json
    python3 build_pdf.py
    python3 verify_manifest.py

The checker prints exactly ACCEPT followed by a newline on success. An
exception is rejection. Instructions are consumed from the end of the JSON
list; the last item initially is the goal. An unused well-typed prefix is
permitted. Both comparison kernels retain the multiline JSON interface.

THE EXACT REFINEMENT
====================
The old update has the shape `a = C and i(t,s) or a` and the new one has
the shape `a = (a, i(t,s))[C]`. The report proves why false results do not
invalidate this change, and why the extra eager operation preserves the
canonical proof compiler. Every new accepted integer/list certificate is
accepted by the old checker. The converse fails on raw certificates:
fixtures/eager_control_only.json is an executed example. Its public goal
still has the ordinary canonical positive proof.

MATHEMATICS AND REFERENCES
==========================
reference/README_pinned.md is the current overview at the revision below.
reference/foundations/ contains inherited LaTeX fragments for the native
logical basis, scalar predecessor, actual-equality reflection, quantifier-free
induction, primitive-recursive compiler, and both internal interpretation
composites. These are attributed reference sources, not newly claimed results.
They are fragments rather than separately compilable standalone documents.

The older inherited_arity_checker.tex describes a historical packet interface.
Do not substitute its old full-native completeness statement for the current
guarded-public contract. The report makes that distinction explicitly.

Source repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Finite tests are evidence about the implementation, not proofs of general
soundness or bi-interpretability. No new Lean or Rocq verification is claimed.

The requested mathematical and all-coordinate complexity breakthrough remains
unachieved in this package. Further research questions are in the report.

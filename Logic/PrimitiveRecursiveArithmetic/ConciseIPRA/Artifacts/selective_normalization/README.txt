SELECTIVE NORMALIZATION FOR iPRA
Research report, reference checker, and a separate compact-checker refinement
Prepared for Vladimir Reshetnikov, November 12, 2026

STATUS OF THE REQUEST

This archive does not establish a construction below all three current
compact-checker minima. At the pinned repository revision, the raw guarded
full-JSON envelope is 249 significant tokens, 271 AST nodes and 477 normalized
UTF-8 bytes, attained by different programs. These recorded minima are upper
bounds from existing programs, not a proved universal lower bound.

The archive contains two distinct results:

1. A selectively normalized six-rule presentation, with the mathematical
   soundness, completeness and bi-interpretation arguments in the report.
   Its readable standalone reference checker measures 2662 / 2904 / 13172
   in tokens / AST nodes / normalized bytes. It is much larger than the
   compact frontier, and no software-size breakthrough is claimed.

2. An independent implementation composition for the existing raw guarded
   calculus: a full-JSON three-field checker measuring 255 / 269 / 605,
   against its matched upstream control's 255 / 271 / 606. It improves
   AST nodes and bytes against that control and improves the displayed
   full-JSON AST coordinate, but it does not beat the token or byte minima.
   It composes the already known floor-product rewriting into the full-JSON
   reader; it deletes no mathematical axiom or inference rule.

The two programs implement different presentations and input contracts.
Their size vectors must not be combined into the size of an imaginary
single checker. The compact program does not implement selective
normalization, and its compact size does not measure the new reference
calculus. No claim of absolute simplicity or global minimality is made.

START HERE

ipra_selective_normalization.pdf    Compiled mathematical report.
ipra_selective_normalization.tex    Report source.
selective/README.txt               Six-rule syntax, scope discipline,
                                   normalizer and complete proof-record API.
selective/selective_checker.py     Standalone closed-theorem checker.
selective/fixtures/                Six valid and ten invalid certificates.
selective/verification.json        Measured sizes and executable evidence.
compact/README.txt                 Exact scope of the independent refinement.
compact/PROOF.txt                  Universal run-equivalence argument.
compact/code/checker269.py         Complete measured compact checker.
compact/controls/checker271.py     Byte-identical pinned upstream control.
compact/PROVENANCE.json            Upstream paths and exact fixture hashes.
notes/recurrence_fusion.txt        Optional shared-recurrence proof refactoring;
                                   the proposed Lean interface is uncompiled.
PROVENANCE.json                    Overall source revision, status and hashes.

REPRODUCTION

From the root of this extracted archive:

    python3 selective/test_selective.py
    python3 compact/verify.py

Examples:

    python3 selective/selective_checker.py < selective/fixtures/closed_all_six_rules.json
    python3 compact/code/checker269.py < compact/tests/local/computation_zero_local.json

Each example prints ACCEPT. The selective example proves

    3 = I(3,0;u.S(u))

using all six primitive rules. This iterator remains irreducible under the
selective normalizer, so the certificate requires genuine rule applications.

The selective reproduction checks 16 certificate cases under normal Python
and Python -O (32 CLI executions), plus capture avoidance, alpha-equivalence,
selective normalization, 60 generated terms and 540 numerical interpretations.
The compact reproduction checks 20 inherited cases, both programs and both
Python modes (80 process executions). The recorded runs have zero failed
expectations. Reproduction refreshes the verification JSON files.

The measured environment is CPython 3.12.14. All source measurements use
ast.unparse(ast.parse(source)) plus a final LF; significant tokens exclude
comments, indentation/dedentation, line separators and the end marker.
All AST nodes, the JSON reader, implemented validation and success output
are charged. The standalone checkers import only the Python standard library.

To rebuild the report with a suitable TeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error ipra_selective_normalization.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_selective_normalization.tex

MATHEMATICAL AND VERIFICATION LIMITS

Selective normalization uses an environment evaluator whose recursive calls
are on strict subterms of the original syntax. Normal forms and substitutions
are compared modulo alpha-equivalence. The primitive rules are Hyp, IS,
VSub, QE, DE and WI; reflexivity is derived from IS at counter 0 with an
identity update. The raw witness syntax selects the WI mode, while judgments
are compared after normalization. The full details and both interpretations
are in the report and selective/README.txt.

The metatheorems are written mathematical proofs. The code is a reference
implementation with finite executable checks; no new Lean or Rocq proof of
the implementation is claimed. No Lean compilation was performed, and no
mechanical translation of arbitrary native derivations is supplied. The
recurrence-fusion note's Lean interface is a proposal, not compiled code or
a demonstrated reduction in Lean source lines.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 12197d86f63e9ec73b2d91399c4de2a8cb0077ee
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The unified article at this revision is the comparison authority; several
older package READMEs have stale frontier values. The compact control and
its inherited fixtures preserve the source repository's MIT No Attribution
license, supplied in compact/LICENSE.txt. Source URLs and hashes are in the
provenance files. All upstream source references identify files at the
pinned repository revision.

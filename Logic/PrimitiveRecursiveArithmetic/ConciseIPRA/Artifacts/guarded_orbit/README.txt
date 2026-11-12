A GUARDED ORBIT PRESENTATION OF iPRA
===================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

RESULT
This is a small further reduction of ConciseIPRA, supported by a new
composition theorem. The compact canonical-input frontier improves from
259 tokens / 283 AST nodes / 526 normalized bytes to 258 / 281 / 525.
These three records belong to DIFFERENT programs. No absolute simplest
axiomatization or dramatic new arithmetic basis is claimed.

Source-selected elimination and root-determined introduction do not compose
inside a strictly guarded proof language: 0=t cannot there yield t=0.
The administrative orbit D_{r,y}(y=I(y,t;u.Su)) repairs the failure. Stable-left
numerical cases and a reversed filter complete the bootstrap. The report
proves both formula composites with the current native Eq/Q/D calculus,
including its direct Q-progress rule. The public theory is equiconsistent
and bi-interpretable with iPRA, with whole numerical domains, actual equality,
and identity numerical composites.

READ FIRST
    ipra_guarded_orbit.pdf       Complete report.
    ipra_guarded_orbit.tex       Single-file LaTeX source.
    CLAIMS.json                 Exact theorem and comparison boundaries.
    code/FORMAT.txt             Public grammar and certificate protocol.

INPUT CONTRACT
Compact kernels assume canonical guarded public statements and permit broader
intermediate formulas. Completeness and round trips are NOT claimed for all
raw administrative formulas. The strict checker includes goal validation:
1205 bytes versus 1208 for the prior guarded interface and 1109 for the prior
scalar interface. It does not beat the old scalar strict comparator.
Universal recognition uses idealized unbounded computation; finite Python
resource limits can reject sufficiently large valid proofs.

COMPLETE PROGRAMS
                               Tokens  AST nodes  Bytes  Gzip-9
    code/checker.py                262       281    606     348
    code/checker_bytes.py          265       303    525     331
    code/checker_tokens.py         258       287    571     339
    code/strict_checker.py         491       563   1205     572

Counts use CPython 3.12.14, docstring removal, ast.unparse plus one newline.
Gzip level 9, mtime=0, is informational. The byte profile's gzip grows one byte.
Raw and normalized gzip sizes and source hashes are in evidence/metrics.json.

REPRODUCE
    python3 reproduce.py
    python3 code/checker_bytes.py < tests/certificates/guarded_equation_induction_local.json
    python3 code/checker_tokens.py < tests/certificates/guarded_equation_induction_global.json
    pdflatex -interaction=nonstopmode -halt-on-error ipra_guarded_orbit.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_guarded_orbit.tex

Acceptance is exit status zero and exactly ACCEPT followed by a newline.
Exceptions reject. The token program needs global certificates; all other
programs need local ones. No checker imports a producer or reference module.
No network is needed. Copied Lean exports are reference evidence, not a
standalone Lean project or a new formalization.

VALIDATION
22 cases x 5 complete programs x ordinary/optimized Python = 220 expected
outcomes, all matched. Four matched predecessor controls also pass: 224 total.
The generic named zero-symmetry derivation has 326 distinct nodes and exactly
one orbit introduction. Its universal closed certificate has 550 instructions.
A separate guarded induction example uses its induction hypothesis.
The strict interface rejects an orbit as a PUBLIC goal while allowing it
inside proofs. See evidence/manifest.json for exact cases and filenames.

This is finite implementation evidence. The new universal theorem is a
written proof reviewed independently within this run, not Lean/Rocq-verified
or externally peer-reviewed. Existing upstream Lean results were inspected,
not rebuilt. The paper gives all primitive axioms, rules, freshness conditions,
both interpretations and composites, and further research questions.

CONTENTS
code/: complete kernels and readable expansion.
tests/: untrusted proof builders, frozen dependencies, local/global certificates.
reference/: earlier checkers, scalar arithmetic sources, theorem exports, license.
evidence/: metrics, validation, provenance, independent review.
measure.py: whole-module metrics; reproduce.py: regeneration and verification.
SHA256SUMS: integrity ledger.

REFERENCE SNAPSHOT
VladimirReshetnikov/ProveIt, 1517d9d79ce33f631e0f82960c849427cbba23bf,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
The scalar basis, arithmetic bridge, source dispatch, guarded padding,
singleton test and arity codec are inherited. The new contribution is their
compatible composition through the orbit bootstrap. No remote changes were made.

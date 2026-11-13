AN EXACT PRESENTATION OF iPRA WITH A SMALLER PROOF CHECKER
13 November 2026

RESULT AND LIMIT
The recommended exact public-syntax checker is 364 significant Python tokens,
424 AST nodes, and 676 normalized bytes. The matching existing exact
canonical-goal reference is 581 / 641 / 1424. The new family's separate minima
are 354 / 399 / 667, attained by different files.

This does NOT beat the global raw-checker envelope 239 / 255 / 460.
It is a smaller implementation of the inherited iPRA presentation, not a
new deletion of arithmetic/logical axioms or a proof of absolute minimality.
The strongest requested target remains unmet. See report.pdf and CLAIMS.json.

WHAT IS NEW
1. A forbidden-slot bit mask is fused into the existing scope traversal,
   replacing the separate exact term/formula validators.
2. A counted, restricted expression reader offers a nontraditional
   certificate syntax. Its character gate excludes input names, calls,
   attributes, strings, and other code constructs before evaluation.
3. The mathematical theory and its full iPRA bi-interpretation are preserved.

START HERE
  report.pdf                complete report
  report.tex                standalone editable TeX, including checker source
  code/checker.py           recommended whole-document exact checker
  code/checker_json.py      exact JSON companion
  code/checker_line.py      smallest byte profile; first input line only
  code/checker_tokens.py    smallest token profile; distinct packet schedule
  code/checker_ast.py       smallest AST profile; distinct packet schedule
  code/checker_matched_json.py   691-byte exact same-object matched reduction
  proofs/                   written universal arguments and independent review
  evidence/                 frozen measurements, verification and source audit
  reference/                pinned controls, selected Lean/article sources
  fixtures/                 simple examples and additional reference cases

RUN
  python3 code/checker.py < fixtures/zero_computation.expr
  python3 code/checker_json.py < fixtures/zero_computation.expr
  python3 code/verify.py
  python3 measure.py
  python3 build_pdf.py

Success is exit status zero and exactly ACCEPT followed by a newline.
Exceptions reject. Run with Python 3.12.14 to reproduce normalized counts.
Fixed interpreter memory/recursion limits are excluded from the mathematical
finite-certificate completeness convention, as in the upstream comparison.

The main reader accepts spaces and LF newlines, decimal integers, minus,
commas and square brackets. It checks the ENTIRE source alphabet before
evaluating its restricted data expression. Every successful stack contains
only exact integers and lists. The JSON companion is supplied if that
reader is preferable. Line profiles read only the first line, ignoring later
lines. Do not use one protocol's certificates in another without its
documented compiler; examples and per-profile fixtures are included.

VALIDATION
The final frozen family passed 224,880 exact-grammar comparisons and
1,006 complete ordinary/optimized Python executions, with no mismatches.
See code/verification.json and evidence/final_verification.json.
The universal written proof is necessary; finite tests are not a substitute.

PROVENANCE
VladimirReshetnikov/ProveIt at
e88ebf229bb61bd870bb229b9c97caaa1e044e6e
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All seven then-current incoming archives are covered by the audit.
Upstream material is attributed in reference/PROVENANCE.json and retains
its MIT No Attribution license. Selected Lean files substantiate the
imported bi-interpretation theorem; their transitive imports are not all
bundled and no new Lean build is claimed.

Verify delivery integrity before rerunning scripts that regenerate receipts:
  sha256sum -c MANIFEST.sha256

PA194NS and PA194SUMS
Research on Vladimir Reshetnikov's ProveIt repository, 14 November 2026 UTC
Pinned ProveIt commit: 1e407ae841e4666f932777fad977ba784ebbcfd5

RESULT
Two new 194-state binary one-tape blank-input constructions.
No construction below 194 was established.
PA194SUMS has an unconditional finite-trace equivalence to primary PA194.
PA194NS has that equivalence to the no-push PA194N source and a corrected
reserved-zero proof compiler. The numerical PA calculus and its mathematical
calibration are inherited, with provenance. No new Lean/Rocq endpoint is claimed.

REPLAY
Python 3.10+ and its standard library:
    python3 verify.py
Do not use Python -O: assertions are checks.
This reconstructs both tables, verifies their SHA-256 digests, checks all source
outcomes with the imported symbolic arithmetic-box interface, replays 32 local
fold cases, and checks complete blank startup.

REPORT
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

SCOPE OF ACTUAL SESSION VERIFICATION
The first checks ran in independent JavaScript ports in functions/V8,
including a positive control reproducing the published primary PA194 receipt.
After the execution environment became available, the supplied Python verifier,
Node.js source checker and Node.js graph audit all ran successfully. The report
was compiled with pdflatex, inspected visually, and packaged with these sources.
See evidence/replayed_verification.json for the complete local Python receipt.

The independent ports agree on every listed source outcome and full startup.
They use the inherited, unchanged register-box lemmas; they are not independent
proofs of those arithmetic lemmas and not newly compiled Lean theorems.

FORMAT
Each .tm row: source read write L-or-R target.
Dense start 0; working states 0..193; halt 194, excluded from state count.
Native start 74; halt 254. Blank symbol 0. No stationary moves.

PROVENANCE
compiler.py and symbolic_runtime.py are unmodified copies from pinned primary
PA194 construction. reference/PA196/Program.lean is the pinned imported PA196
source tree. The old code's machine() helper references files not needed by
verify.py; this replay uses the supplied baseline tables directly.
The James Chang MIT license is retained. Other imported research is credited
through sources.txt and the pinned repository paths.

PACKAGING
    python3 build.py
This verifies, requires pdflatex, compiles twice, and creates a ZIP beside the
source directory. It refuses to overwrite an existing ZIP. Node.js >=18 can
run the independent symbolic suite with node verify.mjs and the full graph
audit with node audit/verify_audit.mjs.

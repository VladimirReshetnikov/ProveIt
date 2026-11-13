SMALLER CHECKED PRESENTATIONS OF iPRA
===================================
Prepared for Vladimir Reshetnikov, 13 November 2026.

Read ipra_checked_reduction.pdf for the complete new report.
ipra_checked_reduction.tex is its LaTeX source.

RESULT
------
Compact, promised public grammar:
  compact/checker_ast255.py       245 tokens / 255 AST nodes / 580 bytes
  Previous matched control:      245 tokens / 256 AST nodes / 580 bytes

Fully validated native public grammar and whole JSON alphabet:
  native/code/checker_tokens315.py   315 / 365 / 618
  native/code/checker_ast353.py      323 / 353 / 630
  native/code/checker_bytes589.py    324 / 367 / 589
  Previous strict envelope:         317 / 356 / 597
  New strict envelope:              315 / 353 / 589

Coordinate order is significant Python tokens / AST nodes / normalized
UTF-8 bytes. Different programs attain the minima. The compact envelope
improves from 239 / 256 / 461 to 239 / 255 / 461; it remains a separate
comparison class from the fully validated family. No single new program
beats every compact coordinate.

These are implementation refinements of the inherited axiomatization.
No arithmetic axiom or logical inference rule has been deleted. The report
states all axioms/rules, logical macros, both interpretation directions,
both round trips, exact new preservation proofs and limitations. The
inherited mathematical bridge is included as the pinned upstream article.
No proof of absolute minimality or new Lean build is claimed.

CONSTRUCTION
------------
The compact checker changes a temporary singleton image [k] to {k}.
Its decoder immediately returns the same list, preserving the exact
accepted streams. This removes one Python AST Load context node.

The validated family composes the known eager opener with an empty-array
administrative premise, native public validation, and context-based phase
selection. The byte program adds a neutral truth only after public goal
validation. The independent numerical scope floor is unchanged.

The validated programs preserve the canonical PUBLIC THEOREM SET, not
every arbitrary raw proof certificate. Canonical major markers 0 become
[]; numerical zeros and other fields are not rewritten. See native/PROOF.txt
and native/translate.py. Public numerical zero in this encoding is code 1;
that is a syntax convention, not an arithmetic equation 0=1.

RUN
---
Python 3.12.14 is the measurement reference.
From this directory:

  python3 native/code/checker_bytes589.py < native/examples/zero_computation.json
  python3 native/code/readable_checker.py < native/examples/zero_computation.json
  python3 compact/checker_ast255.py < compact/fixtures/global_computation_zero.jsonl

A successful run prints exactly ACCEPT followed by a line feed.
An exception or abnormal exit is rejection. Mathematical completeness uses
arbitrary finite resources, as in the inherited programs.

REPRODUCE
---------
  python3 check_manifest.py
  python3 measure_all.py
  python3 compact/verify_set_image.py
  python3 native/verify.py
  pdflatex -interaction=nonstopmode -halt-on-error ipra_checked_reduction.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_checked_reduction.tex

Check the original manifest before regenerating receipts or rebuilding PDFs,
whose timestamps or machine descriptions may differ. Verification does not
need GitHub, a checkout, a network connection or another proof checker.
The optional corpus census in compact/verify_set_image.py accepts a path to
the pinned ConciseIPRA checkout; that optional audit is not an execution
dependency of any measured program.

CONTENTS
--------
compact/                 New AST checker, exact control, fixtures and proof.
native/                  Three validated checkers, readable companion,
                         controls, fixtures, translator, proofs and receipts.
evidence/                Pinned baseline census, measurements, independent
                         reviews, negative regression and document checks.
reference/upstream_article/
                         Attributed article source and original compiled PDF
                         containing the inherited mathematical bridge.
CLAIMS.json              Explicit claims and nonclaims.
SOURCE.json              Repository pin and source provenance.
MANIFEST.sha256           Integrity hashes of the delivered files.

SOURCE
------
https://github.com/VladimirReshetnikov/ProveIt
Commit: 798856e4ef2d02b7f9c0f1660828c5ce58f277f2
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The native calculus, guarded translation, arithmetic bridge, sorted codec,
eager-opening lemma, empty neutral, uniform-zero representation and original
fixtures are credited to ProveIt contributors. The supplied upstream license
is MIT No Attribution. The new refinements have written correctness proofs
and finite executable checks; Python semantics have not been formalized
anew in Lean or Rocq.

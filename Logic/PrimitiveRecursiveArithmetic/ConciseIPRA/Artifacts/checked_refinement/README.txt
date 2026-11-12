SMALLER COMPLETE CHECKERS FOR iPRA
Exact reductions and their limits
November 11, 2026

RESULT

This package supplies three smaller implementations of existing complete
iPRA presentations. It does not establish a new arithmetic or logical
axiom deletion. The request for a further mathematical simplification
remains open; none of the implementation changes is represented as a
mathematical breakthrough.

The comparison includes all three incoming archives in ProveIt at:
  8eb71c1e570e07ef45ead686628e77f18ef34798
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Matched normalized whole-module measurements (CPython 3.12.14):

Program                      Tokens  AST    Bytes  Gzip-9
----------------------------------------------------------------
Compact guarded, old            263   300      521     327
Compact guarded, new            263   303      520     329
Guarded public-goal check, old   489   560     1201     571
Guarded public-goal check, new   407   459      921     507
Native Eq/D public check, old    359   414      803     463
Native Eq/D public check, new    358   413      788     460

The current compact coordinate envelope was 256 tokens / 278 AST / 521
bytes in three DIFFERENT programs. Only its byte coordinate improves,
to 520; the 520-byte program itself has 263 tokens and 303 AST nodes.
Gzip level 9 with timestamp zero is informational, not an objective.

WHICH PROGRAM TO USE

code/checker_native.py
  Full native Eq/D public formulas. The public goal is validated.
  This is the recommended interface for ordinary native formulas.

code/checker_guarded.py
  Canonical guarded public Eq/D formulas. The public goal is validated.
  Proofs may use the inherited auxiliary syntax. Formula round trips
  are claimed for public guarded formulas, not every auxiliary array.

code/checker_compact.py
  The same guarded-public contract, without an included public-goal
  validator. Its smaller byte count must not be compared as though it
  paid for the validated interfaces above.

Each reads one JSON array from standard input, consumes instructions
from the end, and prints exactly ACCEPT on success. Acceptance requires
both exit code zero and exactly the success output. Exceptions are
rejections. These retain the predecessor interfaces, including inert
unused prefixes; they do not newly validate every certificate field as
an exact integer/list tree.

CONTENTS

report.tex, report.pdf
  Explicit native and guarded rule inventories; preservation proofs;
  both interpretation composites; metrics and limitations; further
  research questions; attributed inherited arithmetic appendices.

code/
  Three complete standalone checker modules. They import no producer,
  test helper, proof database, or metric script.

reference/
  Exact matched baselines, current token/AST comparison profiles,
  licenses, foundation proofs and certificate-format documentation.

tests/, reproduce.py
  A portable selected suite and measurement/reproduction program.

evidence/
  Source provenance, measured metrics, deterministic gzip files,
  validation receipts, preservation notes and independent review.

CLAIMS.json
  Machine-readable scope of the result.

REPRODUCE

With CPython 3.12:
  python3 reproduce.py

The portable suite was run after assembly: 39 distinct fixtures, 60
profile/fixture cases, 120 paired comparisons and 240 full processes
across normal and optimized Python. There were 60 accepting pairs,
60 rejecting pairs, zero mismatches and zero timeouts. Development
receipts also record the larger validator-factorization comparisons.
Two reference-only files were subsequently added and hash checked;
their separate receipt records this without changing the earlier
process run's file count.

Build the PDF with a normal TeX Live installation:
  python3 build_report.py

Keep report.tex beside its reference/ directory; the five inherited
appendices are input from their unchanged source files.

ASSURANCE AND LIMITATIONS

The universal implementation arguments preserve the mathematical
certificate relations, abstracting from runtime memory and recursion
limits. A refactoring need not preserve an extreme input's exact
RecursionError threshold. The finite process tests check actual bounded
runs; they do not replace the proofs.

Bi-interpretability and equiconsistency are inherited from the
unchanged theories and the exact proof-checking refinements. Both
numerical domains remain whole, equality is actual equality, and both
numerical interpretation composites have graph x = y.

The repository contains Lean verification of the mathematical native
bridge. The Python codec and the changes here have not received a new
Lean/Rocq verification, and the upstream Lean build was not rerun.
No absolute minimality or external human peer review is claimed.

The source map and licenses attribute inherited material. Descriptions
of older results as "new" inside frozen references belong to their
original documents and are not novelty claims of this package.

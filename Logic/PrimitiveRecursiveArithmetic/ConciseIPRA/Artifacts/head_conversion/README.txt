HEAD CONVERSION FOR iPRA
Research package, 12 November 2026

OPEN FIRST
  ipra_head_conversion_2026-11-12.pdf
  ipra_head_conversion_2026-11-12.tex  (standalone source)

WHAT IS ESTABLISHED
  A six-rule calculus using weak-head conversion of equation endpoints
  and raw substitution hints is exactly equivalent to the inherited native
  scalar calculus on every translated open sequent. Composing with the
  pinned upstream bridge gives equiconsistency and bi-interpretability
  with full first-order intuitionistic primitive recursive arithmetic.
  The numerical domain is unchanged and the comparison map is identity.

  A separate countermodel proves that raw computation equations plus
  variable-only substitution do not recover all native open consequences.

  A compact implementation refinement of the existing guarded calculus
  uses 477 normalized bytes, compared with the incoming 478-byte control.
  This is an encoding improvement, not a new axiom basis.

WHAT IS NOT ESTABLISHED
  This package does not give a new mathematical axiomatization whose
  complete checker improves all the repository's current coordinate
  records. It does not prove absolute shortestness or a complexity lower
  bound. The new proofs are written mathematical proofs, independently
  reviewed and accompanied by executable checks; they have not been
  newly formalized and compiled in Lean or Rocq.

MEASUREMENTS (CPython 3.12.14; entire acceptance modules)
                                  Tokens   AST nodes   Normalized bytes
  Matched full-normalization         1086        1150               3165
  New weak-head checker              1059        1119               3102
  Incumbent token profile             244         272                608
  Incumbent AST profile               249         267                606
  Incumbent byte profile              271         305                478
  Separate byte refinement            272         306                477

  The compact envelope 244/267/478 is attained by different programs.
  The first two validate explicit native open or closed sequents. The
  compact profiles assume finite exact-integer/list input trees and a
  canonical closed guarded public formula. Their interfaces are different.
  The measurement strips docstrings, uses ast.unparse, and adds one LF.

REPRODUCE
  python3 reproduce.py

  Uses only the Python standard library and the included files. Includes
  complete CLI tests both normally and under Python -O. See evidence/ for
  results and FORMAT.txt for the validated native certificate format.
  CPython versions other than 3.12.14 can change normalized source counts.

REBUILD THE REPORT
  python3 build_report.py --compile

  Requires pdflatex and the standard packages named in the main source.
  The script assembles the standalone source from theory/ and runs LaTeX
  twice. The delivered PDF is already compiled. The included upstream
  chapter fragments and Lean endpoint are references, not build inputs.

EXAMPLE CHECK
  python3 code/head_checker.py < tests/head/raw_hint_conversion_bridge.json

  A successful native checker prints ACCEPT and exits with status zero.
  The example is an OPEN SEQUENT: its context is part of the statement.
  A theorem certificate has an empty context. See FORMAT.txt.

COMPACT CERTIFICATES
  python3 code/compact477.py < tests/compact477/candidate/compact_context__computation_zero_local.json

  Consult tests/compact477/cases.json for actual available fixture names.
  Both byte-profile programs consume one JSON array whose last record is
  [goal,0]. Earlier records have [major,source,seed,template]. The candidate
  uses [] for an administrative major; the incumbent uses integer 0.
  code/convert477.py is an UNTRUSTED helper for this representation change.
  Three surplus-arity public truth aliases now reject. They are outside
  the promised canonical public language; no equality of accepted raw
  certificate sets is claimed.

PACKAGE MAP
  code/        Complete checkers, verification programs, measurement script.
  tests/       Actual accepted/rejected proof certificates and controls.
  theory/      Report sections, independent review, unresolved SU note.
  reference/   Pinned upstream sources and the three incumbent programs.
  evidence/    Test results, metrics, provenance, written checker audits.
  CLAIMS.json  Machine-readable distinction between results and limits.
  MANIFEST.json  SHA-256 checksums of the other delivered files.

BASELINE
  https://github.com/VladimirReshetnikov/ProveIt/tree/b9aa36102e523213ae956b474ec651bfde3e5665/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  Includes the ten incoming archives present at that commit.
  Upstream material is covered by reference/LICENSE-ProveIt.txt (MIT-0).

The PDF contains the complete rule inventory, both directions of the new
equivalence proof, the raw-substitution obstruction, the compact alias
argument, the inherited interpretation dependency, and further research
questions. Finite tests are evidence about implementations; the universal
mathematical statements are supported by the written proofs.

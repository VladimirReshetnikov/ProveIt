GUARDED iPRA: TWO VERIFIED CHECKER REFINEMENTS
==========================================
Research note prepared for Vladimir Reshetnikov, 12 November 2026.

Read ipra_checker_refinements.pdf, or build ipra_checker_refinements.tex.

RESULT AND LIMIT
----------------
Two compositions improve the pinned repository's main whole-input compact
checker records. The full normalized Python modules, including reader and
success output, measure as follows on CPython 3.12.14:

                                     Tokens    AST nodes    UTF-8 bytes
checkers/byte476/checker476.py            274          306            476
  matched upstream control              272          306            477
checkers/ast269/checker269.py             255          269            605
  matched upstream control              255          271            606

The main coordinatewise envelope changes from 249/271/477 to 249/269/476.
These coordinates come from different programs. If the distinct line-stream
profiles are admitted too, the envelope is 244/265/476; the 269-node result
does not beat the 265-node stream program.

The underlying guarded scalar calculus and its bi-interpretation with full
first-order intuitionistic primitive recursive arithmetic are inherited.
This is a small improvement of complete checker implementations, not a new
axiom deletion, one checker improving all three coordinates, or a theorem
of absolute minimality. The cited size records are achieved upper bounds,
not proved universal lower bounds. The user's broader mathematical
simplification objective remains unresolved.

CONTRACT AND PROOFS
------------------
The compact programs assume finite exact-integer/list syntax and a
canonical closed guarded Eq/D public goal. They do not independently
validate that grammar or arbitrary JSON. The byte program takes one JSON
array ending in [goal, 0] and four-field proof packets; the node program
takes one JSON array ending in the goal and three-field packets. Both read
packets backward and may leave an unused prefix. ACCEPT followed by a
newline, with normal process exit, is the success convention.

The byte rewrite replaces bool(m or 3 % len(a)) by any((m, 3 % len(a))).
The report proves an array-goal invariant that makes the extra eager length
calculation defined on every successful control run. Thus the two versions
have exactly the same accepted finite integer/list certificates with the
required [goal, 0] header, in ideal execution. Canonical public syntax is
still required for interpreting such a certificate as an iPRA theorem.

The node rewrite replaces
  (k := k - 1) and (s or len(a) == 2) and k
by
  (k := k - 1) * (1 if s else len(a) == 2).
Its proof relates internal False and integer-zero leaves and preserves the
scope allocation, input reads, and acceptance in both directions.

The mathematical presentation, all six guarded rule families, logical
macros, ordinary arithmetic realization, numerical interpretations and
identity comparison maps are stated in the report. Full inherited proofs
are referenced to the pinned upstream chapters, included as source extracts.
There is no new Lean or Rocq verification of the Python runtime or parser.

REPRODUCE
---------
From this extracted directory:

  python3 reproduce.py

This verifies the manifest, checks pinned source identities, remeasures
14 selected baselines and both candidates, and runs 344 isolated checker
processes: 264 in the byte suite and 80 in the node suite. Each fixture is
run with both candidate and control, in ordinary and optimized Python.
The delivered execution had zero failed expectations and zero observed
candidate/control acceptance differences. Finite tests supplement the
written simulations; they are not a proof of soundness or completeness.

Only the Python standard library is used. CPython 3.12.14 is the reference
measurement runtime; normalization can change between Python releases.
The checker code requires Python 3.8 or later for assignment expressions;
the audit tools require Python 3.9 or later for ast.unparse.

To compile the report as well, with a normal TeX Live or MiKTeX installation:

  python3 reproduce.py --pdf

This runs pdflatex twice. Required LaTeX packages are named in the TEX
preamble. The report includes its candidate source files using relative
paths, so compile from this directory. Reference chapter extracts are not
standalone build targets.

A direct certificate example:

  python3 checkers/byte476/checker476.py < checkers/byte476/proof_zero_computation.json

Its goal is I(0, S(S(0)); u.S(0)) = S(S(0)); expected output is ACCEPT.

CONTENTS
--------
ipra_checker_refinements.tex/.pdf  Report, proofs and complete candidate code.
checkers/byte476/                 476-byte program, control, 40 unique payloads,
                                  66 labels, verifier, provenance and review.
checkers/ast269/                  269-node program, control, 19 unique payloads,
                                  20 labels, verifier, proof and review.
reference/baseline_audit/         Selected pinned baseline programs and audit.
reference/upstream/               Relevant source chapters, README and license.
CLAIMS.json                      Explicit claims, scope and nonclaims.
verification_receipt.json        Summary of the delivered reproduction run.
MANIFEST.sha256                  SHA-256 checksums of delivered files.
reproduce.py                     Offline reproduction entry point.

The manifest records the delivered bytes. Reproduction checks it before
running and updates generated receipts. Rebuilding the PDF may change its
bytes because of TeX timestamps; this does not change the original manifest.
The --skip-manifest option permits a subsequent run after generated outputs
have intentionally changed.

PROVENANCE AND LICENSE
----------------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 6874c85a4cea45d881de73620284fcc75d740942
Root: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/
The report uses the integrated article's contract-separated comparison,
not an exhaustive new census or the shorter, partly superseded README table.

The original files and adaptations are distributed with the repository's
MIT No Attribution license, preserved in reference/upstream/LICENSE-ProveIt.txt.
No remote repository was modified.

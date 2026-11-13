FIXED-POINT LAWS, INDUCTION, AND A 241-TOKEN iPRA CHECKER
Research report for Vladimir Reshetnikov, 12 November 2026

STATUS
This is a partial result toward the requested simplification. It does not
claim a new smallest axiom basis or one checker below all current records.

1. The complete compact checker has 241 significant Python tokens,
   267 AST nodes and 566 normalized UTF-8 bytes. The prior coordinate
   minima were 242 / 262 / 469, attained by different programs. The token
   reduction preserves the existing calculus and its inherited
   whole-domain, actual-equality bi-interpretation with full first-order
   intuitionistic primitive recursive arithmetic.

2. A new countermodel answers a question in the current article:
   preservation of every fixed point cannot replace equation induction.
   The strengthened model also validates the seed-shift law, the canonical
   successor iterator, and commutative cancellative addition. The full
   argument is a written mathematical proof, not a finite-model search
   or a Lean/Rocq verification.

START HERE
  ipra_fixed_points_and_checker.pdf  -- compiled report
  ipra_fixed_points_and_checker.tex  -- complete standalone LaTeX source
  CLAIMS.json                        -- exact scope of the claims

CHECKER
  code/checker_tokens241.py          -- complete new compact checker
  code/control_ast262.py             -- exact comparison control
  code/control_tokens242.py          -- exact old token record
  code/fixtures/                    -- fourteen attributed test streams
  code/verify.py                    -- 84 isolated regression executions

Input is one JSON goal line followed by three-field JSON instruction
records, one per line. The compact contract promises a canonical closed
guarded Eq/D goal and finite exact-integer/list certificate data. Unused
suffixes are permitted. This program is not a validator for arbitrary
JSON, and the 241-token count must not be compared with fully validating
programs as though the contracts were identical. Resource-unbounded
execution is idealized as in the repository comparison.

REPRODUCE
Use CPython 3.12.14 to reproduce the exact normalized-source metrics:

  python3 reproduce.py

This remeasures the complete modules, reruns the checker fixtures, and
runs finite sanity checks for the explicit seed algebra. The seed checks
do not prove the infinite model-extension argument. The written proofs
establish the unbounded claims; executable checks are supplementary.

To rebuild the PDF with an ordinary TeX Live installation:

  pdflatex -interaction=nonstopmode -halt-on-error ipra_fixed_points_and_checker.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_fixed_points_and_checker.tex

PROVENANCE
Comparison repository: VladimirReshetnikov/ProveIt
Pinned commit: 6874c85a4cea45d881de73620284fcc75d740942
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All twelve incoming archives were checked against their pinned Git blob
identities. Reference programs, archive hashes, source links, and full
measurement/test results are retained under reference/ and evidence/.
Reference code is provided under the repository's MIT No Attribution
license, copied as reference/LICENSE.txt.

No repository changes or publication are part of this deliverable.

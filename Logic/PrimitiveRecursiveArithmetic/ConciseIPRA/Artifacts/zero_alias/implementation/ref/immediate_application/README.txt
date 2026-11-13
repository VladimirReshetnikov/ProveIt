A SMALLER CHECKED PRESENTATION OF iPRA
Immediate substitution, exact acceptance, and the limits of the reduction
Prepared for Vladimir Reshetnikov, November 12, 2026

RESULT AND LIMIT

The compact complete checker decreases from 487 to 479 normalized UTF-8
bytes. A fully validating native companion decreases from 646 to 637.
Both changes preserve their exact reference acceptance relations, including
the ordering of every scope-sensitive operation. The proof is universal;
the included 121-case suite gives additional executable evidence.

THE FULL REQUESTED TARGET HAS NOT BEEN ESTABLISHED. No logical or arithmetic
axiom is deleted, no absolute minimality is claimed, and the independent
248-token and 270-AST-node frontier records remain unbeaten. The new compact
family envelope is (248,270,479), attained by different programs. The actual
new compact program has vector (272,304,479), not the envelope vector.

The package fully specifies the inherited scalar theory and both its logical
and nonlogical rules. Its ordinary realization is bi-interpretable and
equiconsistent with full first-order intuitionistic primitive recursive
arithmetic, with whole numerical domains, actual equality, and both numerical
composites internally the identity graph x=y. The report reproduces the
detailed inherited foundational chapter, with attribution, and explains the
full formula round trips. All 97 upstream Lean module sources are included;
the upstream Lean development was not rebuilt in this run.

START HERE

ipra_immediate_application.pdf   Compiled report with foundational appendix.
ipra_immediate_application.tex   Complete standalone LaTeX source.
code/checker637.py               Validates the entire integer/list alphabet
                                and the closed native Eq/D public goal.
code/checker479.py               Smaller compact guarded-goal interface.
CLAIMS.json                     Precise claims and explicit limits.
evidence/verification.json       Exact measurements and every test result.

COMPLETE MODULE METRICS

Program                         Tokens   AST    Normalized bytes
controls/checker487.py             276    308           487
code/checker479.py                 272    304           479
controls/checker646.py             343    392           646
code/checker637.py                 344    392           637
controls/tokens248.py              248    277           609
controls/ast270.py                 254    270           608

Metric: CPython 3.12.14, complete module, ast.unparse plus one final LF;
significant Python tokens, all AST nodes, UTF-8 bytes. Reader, inference,
any included validation, and success output are counted. No compressed
payload or proof-specific imported dependency is used by the checkers.

RUN

  python3 code/checker637.py < tests/native/proofs/computation_zero_local.json
  python3 code/checker479.py < tests/byte/context/computation_zero_local.json
  python3 verify.py
  python3 build.py

The examples print ACCEPT. The verifier reproduces six size vectors, two
four-part AST audits, and 484 isolated executions (121 cases x 2 programs x 2 modes),
with zero failed expectations in the delivered run. Normal and optimized
Python are both checked. Build requires an installed TeX distribution with pdfLaTeX.
There are no network requirements for reproduction. Verification and building
refresh derived evidence, so verify MANIFEST.sha256 before rebuilding.

INPUT CONTRACTS

Each candidate uses multiline JSON with a list of four-field packets followed
by the public goal, consumed from right to left. Acceptance is normal exit and
exactly ACCEPT followed by a newline. Exceptions reject. Unused prefixes are
permitted, as in the references.

checker479 assumes finite exact-integer/list data and a canonical closed
guarded Eq/D public goal. It does NOT independently validate that public
grammar. checker637 validates the whole alphabet, including unused data, and
the full closed canonical native Eq/D public goal. These are different
contracts. The three-field token/AST controls have yet another protocol and
one-line JSON framing; their certificates are not interchangeable with the
four-field examples.

NEW NEGATIVE RESULT

Simply relaxing the native public validator to treat raw numerical coordinates
1 and 2 as additional spellings of zero loses completeness. The unchanged raw
checker is sound when those coordinates denote arbitrary fixed constants.
Thus it cannot prove the raw equation [1,0], although the proposed zero-alias
reading makes it 0=0. This rules out that specific validation deletion. It is
a written semantic proof, not a mechanized theorem or universal lower bound.

PROVENANCE

Repository: VladimirReshetnikov/ProveIt
Commit: 36d37fc1071fe289371f6bcd7dcfa0eac593a5a6
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All nine current incoming archives were inspected in addition to filed work.
PROVENANCE.json records exact selected paths and hashes.

The inherited mathematics and controls retain the repository's MIT No
Attribution license; the new material may be used under the same license.
No new Lean/Rocq verification of the Python implementation is claimed.

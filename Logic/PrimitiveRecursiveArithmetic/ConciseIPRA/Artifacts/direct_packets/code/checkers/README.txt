PACKET ARGUMENTS AND STRUCTURAL MATCHING FOR THE CONCISE iPRA CHECKER
==================================================================

The mathematical axiomatization is the inherited guarded scalar iPRA
presentation. This package gives source-level reductions of its complete
standalone Python proof checkers and proves that the represented public
theory is unchanged. It does not claim a new arithmetic or logical axiom
deletion or an absolute minimality theorem.

Whole-JSON coordinate envelope (different complete programs):
  inspected baseline: 248 tokens / 268 AST nodes / 469 normalized bytes
  this package:        246 tokens / 263 AST nodes / 465 normalized bytes

The JSONL AST companion reaches 259 AST nodes, below the mixed-format
262-node frontier. The mixed-format 241-token record is not improved.

FILES
-----
checker.py                  465-byte whole-JSON byte profile
readable_checker.py         Standalone readable expansion of that profile
control.py                  Exact 469-byte byte-profile control
translate.py                Root framing bijection for that profile
checker_tokens_json.py      Whole-JSON token profile, 246 tokens
checker_ast_json.py         Whole-JSON AST profile, 263 nodes
checker_ast_jsonl.py        JSONL AST profile, 259 nodes
control_tokens241_jsonl.py  Exact JSONL token control
control_ast262_jsonl.py     Exact JSONL AST control
control_tokens248_json.py   Prior whole-JSON token-envelope representative
control_ast268_json.py      Prior whole-JSON AST-envelope representative
translate_stream.py        JSONL/whole-JSON parsed-record reversal
PROOF.txt                  Argument-packet and Boolean-return proof
PROFILES_PROOF.txt          Pattern binding, framing and profile proof
verify.py                  Byte-profile metrics and 71 CLI executions
verify_profiles.py         Other metrics and 255 CLI executions
verification.json          Recorded byte-profile results
profiles_verification.json Recorded other-profile results
fixtures/                  Substantial inherited four-field certificates
stream_fixtures/           Substantial inherited three-field certificates

Each measured module includes its own parser and acceptance output and
imports only Python's standard JSON module. None imports another checker,
translator, theorem list, compressed source or code generator.

CONTRACT
--------
These are COMPACT profiles, with the existing canonical closed guarded
Eq/D public-goal and exact integer/list proof-data promise. They are not
the native public-goal-validation or whole-input-alphabet-validation
profiles. All new input formats and equivalence domains are documented in
the two proof notes. Ordinary finite execution with exactly ACCEPT plus LF
is acceptance; exceptions reject.

REPRODUCE
---------
Use CPython 3.12.14 for the exact published metric convention:

  python3 verify.py
  python3 verify_profiles.py

The controls and fixtures are attributed to the user's ProveIt ConciseIPRA
corpus; see the proof notes and upstream license. The existing full
first-order iPRA bi-interpretation is inherited unchanged through exact
preservation of public goals and their theorem set. No Lean or Rocq
verification of these Python changes is asserted.

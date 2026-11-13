A WHOLE-JSON CHECKER WITH 269 AST NODES

This directory contains a standalone implementation composition for the
existing guarded public presentation of intuitionistic primitive recursive
arithmetic. It is an AST-only improvement to the current compact benchmark,
not a new arithmetic theory and not a globally smallest proof checker.

Files
-----
checker_ast269.py             Selected complete checker.
controls/checker_ast271.py    Exact matched repository control.
PROOF.txt                    Written equivalence argument and limits.
verify.py                    Portable standard-library reproduction harness.
fixtures/positive/           13 inherited positive regression certificates.
fixtures/negative/           7 inherited adversarial certificates.
evidence/validation.json     Metrics and all 80 CLI results.
PROVENANCE.json              Pinned repository sources and SHA-256 hashes.
LICENSE.txt                  Repository MIT No Attribution license.

Run
---
  python3 checker_ast269.py < fixtures/positive/computation_zero_local.json
  python3 verify.py

An accepting checker execution exits with status zero and prints exactly
ACCEPT followed by a newline. Exceptions reject. The checker reads one whole
JSON value, including ordinary multiline JSON. It uses no theorem-specific
external import or compressed payload.

Metrics
-------
Complete normalized modules, CPython 3.12.14:

                                Tokens   AST nodes   UTF-8 bytes
controls/checker_ast271.py          255         271           606
checker_ast269.py                   255         269           605

Normalization is ast.unparse(ast.parse(source)) plus one final LF. Tokens
exclude only comments and layout. All AST nodes, input parsing, proof
checking, and success output are counted. The unchanged input contract is
finite exact-integer/list certificate data and, for the iPRA public theorem
claim, a canonical closed guarded public goal. This compact checker does not
independently validate that public grammar or the complete JSON alphabet.

The supplied 13 positive regressions exercise computation, transport,
introduction, compound reasoning, and induction using its hypothesis; some
have auxiliary native Q goals rather than public Eq/D goals. Seven negative
regressions cover contradiction, missing computation, wrong endpoints,
future-name capture, branch leakage, wrong packet arity, and a missing goal.
Both modules run on all 20 cases in normal and optimized Python, for 80
standalone checks. All expected outcomes matched in the delivered run.

The reduction
-------------
The selected checker composes the whole-JSON reader of three_field with the
already proved selector of fused_iteration. It replaces

  (k := (k - 1)) and (s or len(a) == 2) and k

by

  (k := (k - 1)) * (1 if s else len(a) == 2)

The only possible value difference is False versus integer 0. The code makes
no exact-type or identity tests on these values. PROOF.txt gives the precise
simulation and preserves the order of all scope-sensitive operations.

What is and is not established
------------------------------
The accepted raw integer/list certificate executions agree with the matched
control, up to Boolean/integer aliases. Consequently the same guarded public
theorems and their inherited whole-domain bi-interpretation with iPRA are
preserved. This is a written simulation proof supported by finite execution
checks. No new Lean/Rocq verification of the Python implementation is claimed.

This program improves the AST minimum from 271 to 269 in the documented
whole-JSON compact profile. It does not improve its 249-token or 477-byte
minimum. Those minima are attained by different programs. This package does
not claim a new mathematical axiomatization or a mathematical lower bound.

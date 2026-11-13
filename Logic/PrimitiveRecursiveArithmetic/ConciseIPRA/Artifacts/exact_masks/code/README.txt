EXACT CANONICAL iPRA CHECKERS
===========================

Recommended entry point:

    python3 checker.py < examples/zero.json

The main checker consumes the entire document. Its restricted expression
reader permits decimal integers, minus signs, square brackets, commas,
spaces, and newlines. It gates the complete text before evaluation. It
therefore accepts ordinary integer/list literals as well as harmless
integer subtraction, repeated unary minus, and list-indexing expressions.
No name, string, call, attribute, assignment, multiplication, or other
executable facility can pass the character gate. The resulting certificate
must be a list of integer/list trees. The public goal is its final item.

The exact public grammar excludes references to padding slots: only
genuine bound variables may occur. The inherited inference kernel is
unchanged after this one syntax-checking phase. The report proves the mask
invariant and correspondence to the canonical native theory and iPRA.

Successful checking prints exactly ACCEPT. An exception or any other
termination is rejection. The programs contain no assertions, so -O
does not disable checking. Mathematical completeness concerns arbitrary
finite computations; actual Python implementations have resource limits.

Frozen complete modules, normalized with ast.unparse plus one final LF:

    file                 tokens   AST nodes   bytes   input
    checker.py              364         424     676   whole expression
    checker_json.py         365         428     687   whole JSON
    checker_line.py         359         420     667   first line expression
    checker_tokens.py       354         416     734   first line expression
    checker_ast.py          361         399     759   first line expression

Different programs attain the three family minima: 354 / 399 / 667.
The main whole-document program is 364 / 424 / 676.
The existing exact canonical reference is 581 / 641 / 1424.
This is an exact-interface implementation improvement, not a new deletion
of arithmetic axioms or a proof of an absolute complexity minimum.

The line profiles consume only the first physical line; subsequent input
is ignored. Use the whole-document main checker for a file whose entire
contents should be checked. The JSON counterpart imports only Python's
standard JSON module and retains the ordinary JSON text contract.

The token and AST profiles use a three-field certificate protocol that
differs from the main four-field protocol. Their respective examples are:

    python3 checker_tokens.py < examples/zero_tokens.proof
    python3 checker_ast.py < examples/zero_ast.proof

The JSON and line-byte programs share the main example:

    python3 checker_json.py < examples/zero.json
    python3 checker_line.py < examples/zero.json

To reproduce the frozen metrics and checks:

    python3 verify.py

The final run performed 224,880 grammar comparisons and 1,006 complete
normal/-O checker executions, with zero mismatches. The fixtures include
14 canonical positive proofs per protocol, covering both computations,
equality transport, implication, witness/closure elimination, and induction
whose hypothesis is used. Padding, type, scope, false-goal, reader, and
protocol mutations are included. These tests support the implementation;
the universal correspondence rests on the mathematical proof.

metrics.json records measurements and SHA-256 hashes of every measured
standalone source. verification.json records the complete final run.
None of the five measured checkers imports verify.py, fixtures, or any
other uncounted helper.

PROVENANCE
----------

The underlying inference protocols and proof fixtures come from
VladimirReshetnikov/ProveIt, pinned commit
e88ebf229bb61bd870bb229b9c97caaa1e044e6e, ConciseIPRA incoming package
ipra_scope_phase_2026-11-13. Its relevant files are
code/checker_bytes584.py, code/checker_tokens302.py, code/checker_ast340.py,
and their matching certificates/*.json files.

The comparison grammar is the exact canonical entry point in the incoming
package ipra_composition_and_dummy_slots_2026-11-13, code/checker_exact.py.
Every fixture file records the SHA-256 of its originating source and the
precise conversion of its expected outcome to the exact-goal contract.
The new work fuses the exact predicate with the opener, using a bitmask,
and composes it with the explicitly counted restricted expression reader.
No fresh Lean verification is claimed for these Python changes.

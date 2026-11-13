COMPACT CHECKER REFINEMENTS
==========================

Run from this directory:

  python3 code/token239.py < fixtures/global_guarded_induction_with_used_hypothesis.jsonl
  python3 code/checker.py < fixtures/global_compound_implication_elimination.jsonl
  python3 code/readable.py < fixtures/global_computation_successor.jsonl
  python3 verify.py

Complete-module CPython 3.12.14 measurements
-----------------------------------------

                         tokens  AST nodes  normalized UTF-8 bytes
controls/checker240.py       240        266                    551
code/token239.py             239        261                    549
code/checker.py              246        257                    589

These are standalone complete modules, including JSON parsing and ACCEPT
output. No project module, hidden proof engine, source string, compressed
program, or omitted lookup table is imported. Normalization is ast.unparse
of the complete module plus one LF. Significant tokens exclude comments,
encoding/end markers, newlines and indentation/dedentation tokens.

The independent current corpus envelope is 240 tokens / 259 AST / 462 bytes,
attained by different programs. The new envelope is 239 / 257 / 462, again
attained by different programs. There is no new byte minimum, no single
program below every coordinate, and no claim of absolute mathematical
minimality or a new deletion of an arithmetic or logical axiom.

Input contract
--------------

The first line is a canonical closed guarded Eq/D public goal in the
inherited arity encoding. Each consumed later line is one three-field
packet [source, seed, template]. Certificate trees contain exact integers
and finite lists. Unused trailing lines are allowed. Success means normal
exit with exactly ACCEPT followed by LF. Exceptions reject.

The compact source assumes this public-syntax and alphabet promise; it
does not validate every aspect of arbitrary JSON. The AST profile rejects
non-sequence packets by its match statement, but is not thereby a full
grammar validator. Standard physical Python resource limits may reject
valid large certificates; completeness refers to ideal unbounded execution.

Transformation
--------------

The previous substitution-image expression was

  c(g, s) or k * bool(s or len(a) == 2)

The new expression is

  (c(g, s) or s or len(a) == 2) and k

Both first check the same recursive major; on success c returns None.
The floor k is then read after that recursive call's reservations. If s
is true, both omit len(a); otherwise both evaluate len(a)==2. A true
condition gives k in both programs. A false condition gives integer 0
in the control and Boolean False in the candidate.

Every operation in the checker respects the relation identifying False
and 0 recursively in lists: comparisons, truth tests, arithmetic, list
construction/replication/slicing, membership, and the recursive opening.
Iteration and len fail on either scalar. There is no type, identity,
representation, hashing, or serialization test inside the measured proof
engine. Induction on finite executions therefore gives identical
acceptance, record consumption, floors, and recursive-call traces modulo
that relation. The new theory has the same public theorem set as the
unchanged control. Its iPRA correspondence is inherited.

The AST profile additionally composes two existing implementation ideas:
definition-time k=0 is moved into the opener's default d=(k:=0), and
three-field unpacking is expressed by a sequence pattern. The first has
identical state before checking starts. On an exact integer/list packet,
the second either binds exactly the same three fields and whole packet,
or rejects because a field remains unbound. These changes introduce no
new arithmetic rule.

Validation and provenance
-------------------------

verify.py executes the exact control, both compact candidates, and the
readable expansion normally and with -O: 256 subprocess checks cover 14
inherited fixtures, false public goals, malformed packets, and truncated
input. All expectations pass. The long positive examples use genuinely
used induction and compound logical elimination. Scope attacks include
future witnesses before the recursive major and context leakage.

The same script compares 224 exact-integer/list mutation cases using the
correct two-argument c(context,goal) interface. It compares recursively
recorded call states modulo False=0, record consumption, floor, and
acceptance; all comparisons pass. The comparisons exercise generated
False leaves, rather than only branches where both images are k.

Two AST checks verify that precisely the claimed transformations separate
the three compact modules. Finite tests support the written simulation;
they do not prove the inherited arithmetic soundness or bi-interpretation.

PROVENANCE.json names the pinned upstream archive, exact member, source
hash, inherited fixtures, and the corpus novelty comparison. The original
MIT-0 license and prior fresh-return reservation proof are retained under
reference/. No new Lean or Rocq verification is claimed.

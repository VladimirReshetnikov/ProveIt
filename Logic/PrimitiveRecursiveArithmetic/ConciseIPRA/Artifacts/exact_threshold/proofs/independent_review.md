# Independent review of `exact_threshold.py`

Candidate SHA-256:
`f295e9d65430eadba361d8f4b77ddbe96b1c1005d48b12a103f3cc67a0a14b92`.

Measured under CPython 3.12.14 after `ast.unparse` plus LF:
**314 significant tokens / 357 AST nodes / 590 UTF-8 bytes**.

This is below each coordinate of the observed exact-canonical envelope
316 / 358 / 591. It is not below the compact promised-grammar envelope or
the sorted-only envelope, and it is an implementation/protocol refinement
of the existing calculus, not a new arithmetic axiom deletion.

## Precise changes relative to intrinsic validation

The opener `i`, its default image, actual-binder depth increments, public
grammar guard, scope checks and all rule-side validation remain AST-identical
to the 316 / 360 / 591 intrinsic-validation baseline. The changes are:

1. The candidate evaluates `i(t,s)` only when the equality/closure template
   comparison selects that source instance. The baseline built both tuple
   alternatives eagerly.
2. The equation-progress flag changes from `len(a)==2==u` to
   `len(a)==2>u`. The latter is Python's chained comparison, equivalent to
   `len(a)==2 and 2>u`.
3. The fixed reader is written with `import json` and a walrus binding of
   the list's `.pop` method inside the initial call. This changes no parsed
   values or proof-rule evaluation order.

## Soundness of the threshold

The rule selected when the major is neutral is still either native DI by
cases or native DI by equation progress. Progress is selected only if the
opened matrix has exactly two children. Under the inherited raw reading this
is a literal equation. Any JSON numeric mode below 2 may select that rule;
whether it is a negative integer, Boolean or nonintegral finite number does
not change the arithmetic premise. All remaining successful modes select
the case rule. Incomparable mode values can raise an exception and reject;
they do not introduce any additional rule.

No compound matrix can acquire induction: the first conjunct
`len(a)==2` is false at a `D`/`Q` matrix. The already proved positional-arity
guard at `i(*a,t,2)` still excludes introduction from an equation goal. Its
three-argument limit is unchanged.

Thus the call-tree soundness induction uses exactly the same native inference
rules. The threshold only changes the certificate spelling that selects two
already justified rules.

## Soundness of lazy source opening

The opener has no side effects: it neither reads proof packets nor changes
the global scope counter. If the matching comparison is true, both the
target instance `i(t,u)` and the selected source instance `i(t,s)` are still
evaluated at the same current floor, and the major is still checked. The
standard opening lemma justifies transport or closure specialization.

If the comparison is false, the continuation goal is the unchanged `a`.
The unused source instance is neither retained as a hypothesis, returned as
a conclusion, nor used to justify an inference. A discarded-source failure
therefore need not reject this branch. The context contribution still comes
from the proved major and the checked opening of that major, or from the
checked introduction premise. The target-instance comparison is retained.

The new checker can consequently accept raw packets rejected by the eager
baseline. This does not imply unsoundness, but it rules out claiming equality
of their complete raw byte languages.

## Native completeness compiler

Use the existing canonical native proof compiler, preserving all terms,
formulas, scope names, proof-tree shape, packet order and theorem codes.
Only the mode field of an actual introduction with a literal equation
matrix changes:

| Native rule | Old canonical mode | New canonical mode |
| --- | --- | --- |
| Equation progress | 2 | 0 |
| Equation case introduction | 0 (or any old non-2 case flag) | 2 |
| Compound case introduction | unchanged | unchanged |

This must be a proof-tree-aware or trace-aware transformation. Replacing all
integer occurrences 0 and 2 would corrupt numerical codes and computation
fields.

At an introduction packet the public/working conclusion is unary, so changing
the mode cannot make its initial equation-shaped computation candidate match.
The canonical neutral major is the empty list and is unchanged. The retained
premise is identical because old `u==2` and new `u<2` have the same selected
truth value after the translation. The term/formula opener is unchanged.
The canonical numerical witness has no binary root, whereas the equation
matrix has a binary root, so the changed unused target-instance probe cannot
activate equality transport. With the standard empty-list neutral major the
major-match test is false in any event. Canonical fields keep every required
probe defined. The induction hypothesis therefore translates the continuation
with the same statement and scope.

All other inference packets remain unchanged. Lazy evaluation removes only
irrelevant checks, so an old canonical successful source opening cannot cause
a new rejection. This proves canonical completeness by the existing native
proof-tree induction. The numerical domain, actual equality, and both
interpretation round trips remain those of the inherited native/iPRA bridge.

The public `true` alias for zero code 1 remains legitimate: every relevant
numeric comparison and truth test agrees with 1, and the canonical modes 0
and 2 are unchanged by replacing numerical-zero leaves with `true`.

## Independent executable evidence

The test source from the intrinsic-validation package was copied into
`threshold_validation/`, with only the candidate module and the translated
positive-fixture table substituted. Its independent recursive public grammar
is separate from the candidate's compact opener. The candidate's opener AST
was independently checked equal to the baseline opener AST.

- 14 positive native derivations were translated and accepted.
- 12,742 public-grammar comparisons had no mismatch.
- 13,120 opener checks produced no active-value type violation.
- 490 intended positive aliases/prefix variants all accepted.
- 10,866 false or invalid export mutations produced no false acceptance.
- 232 complete ordinary/optimized Python executions had no unexpected result.
- An additional 90 future-witness capture trials varied the new threshold mode
  and negative/fractional parameter spellings; every trial rejected.

The reciprocal raw-language comparison found four original fixtures rejected
by the new module and the four translated fixtures rejected by the old module:
used equation induction, an atomic case introduction, and two all-number
zero-symmetry proofs. This is expected evidence of the protocol change,
not a defect. Their theorem codes are identical and the translated proofs
are checked independently by the new module.

Receipts:

- `threshold_validation/PROVENANCE.json`.
- `threshold_validation/tests/verification.json`.
- `threshold_protocol_comparison.json`.

These tests supplement the written structural argument. They are not a Lean,
Rocq, or CPython execution formalization.

## Review outcome

No new soundness or completeness defect was identified in this candidate.
The threshold and lazy-opening arguments are sufficient to adapt the existing
native call-tree proof and canonical compiler. Claims should remain local:
an exact-public-interface checker improvement, with a changed certificate
protocol and inherited full iPRA bi-interpretability. The stronger requested
global-frontier construction remains unestablished.

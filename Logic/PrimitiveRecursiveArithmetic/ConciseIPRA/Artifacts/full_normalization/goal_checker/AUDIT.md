# Independent audit of the expression-form checker

The audit covers `code/full_expression_checker.py`, including its header decoder,
shared traversal, normalizer, automatic leaves and four non-leaf proof packets.
No soundness defect was found in the inspected implementation. This is a written
code audit supported by the finite checks in `evidence/verification.json`; it is
not a proof-assistant verification of Python.

## Input typing and the Python equality boundary

1. The header is an exact dictionary with the four documented keys. The numerical
   scope is an exact integer, explicitly excluding Boolean aliases, and is
   nonnegative. The retained context is an exact list.
2. Every syntax node is an exact nonempty list before unpacking. The tag is checked
   against the required numerical/formula sort and must be a key in the finite
   signature table. A non-string tag cannot name a constructor. Unhashable tags
   raise TypeError; unknown hashable tags raise KeyError. Neither reaches success.
3. The signature table checks exact arity before recursively visiting children.
   Each child is visited in its required sort and with exactly the number of
   new binders prescribed by that constructor.
4. The variable callback checks `type(i) is int` and `0 <= i < n+d`.
   Thus Python's `True == 1` and `False == 0` equalities cannot admit Boolean
   variable coordinates. The internal comparison of a Boolean sort indicator
   with the internally supplied values 0/1 is intentional; no user value supplies
   the sort argument.
5. Every public context formula and every current goal is validated before a
   hypothesis or reflexivity test. Consequently structural equality is compared
   only on correctly sorted, scoped and canonical syntax at those acceptance
   points. Numeric aliases such as 0.0 and False cannot forge a syntactic term.
6. The walker recursively validates all original children before erasing an
   iterator redex. Ill-scoped or ill-sorted data in a computationally unused
   initializer/body are therefore not hidden by normalization. Dedicated
   rejection fixtures cover this case.

## Every used rule parameter

- QE validates the numerical target and checks the displayed Q major; the latter
  validates its body in the extended scope before either instance is used.
- DE checks the displayed D major. The new Q assumption is well formed in the
  new numerical scope. The old goal has already been validated before that
  variable is introduced, and the continuation must prove its capture-safe
  lift, preventing eigenvariable escape.
- DI starts from a validated D goal and separately validates its witness. Its
  progress/case selection tests an actual equation root and the actual normal
  zero term. The branch target and hypothesis are generated only by the shared
  capture-safe substitution and shift operations.
- Tr checks its displayed source equation, then validates the term template in
  scope n+1. It compares the generated target endpoint with the already checked
  goal and recursively checks the generated minor equation. Supplied sources,
  targets and templates cannot enter substitution unchecked.

Every continuation context contains either validated old formulas shifted into
its new scope, or the appropriately opened body of a checked major/goal. The
implementation never accepts a user-supplied continuation context.

## Normalization and substitution

The three conditional cases are zero computation, successor computation, and
an unchanged non-redex. The successor case constructs the predecessor iterator
and substitutes it for the state variable of the body. The inserted iterator
need not already be normal: substitution invokes the same typed traversal via
capture-safe shifting on every inserted image. If the state variable is absent,
the unused image is not evaluated. This is the intended normalization algorithm.

Shifting protects indices below the local binder depth. Substitution replaces
exactly the index at that depth, shifts its image under those binders, and
adjusts external indices by `drop`. The DI successor instance uses `drop=0`
because the fresh step parameter replaces the old quantified position.
The numeric/formula signature is shared by validation and these operations,
removing an independent binder table that could disagree with the validator.

The mathematical correctness of recursive normalization relies on the separate
termination/confluence argument in the report. The audit does not replace that
argument with testing. The finite receipt includes comparison with the separate
forward implementation for normalization, lifting, and substitution.

## Ignored data, rejection and resource limits

A validated hypothesis or reflexive equation closes without inspecting its
`proof` field. Arbitrary JSON there, including strings, Booleans, objects or
Python JSON's nonfinite numeric aliases, is intentionally ignored. Such data
cannot alter a validated theorem. The interface does not claim to typecheck
unused proof payloads. `null` is the documented canonical leaf spelling.

At a non-leaf, the sequence patterns require the exact opcode and arity.
Unknown opcodes, extra arguments and malformed supplied parameters reject.
The top-level parser follows Python JSON semantics, including last-value-wins
for duplicate object keys; the resulting object must have the exact four-key
header. No eval, dynamic code execution, external database or proof oracle is
used. No check is an assertion, so Python's -O flag removes none of them.

The only success output occurs after the entire check returns. Uncaught I/O or
resource exceptions also fail the documented acceptance condition. Termination
of mathematical normalization does not imply practical time or memory bounds;
large certificates can exhaust the interpreter and are then rejected by this
finite implementation.

## Scope of the comparison

The matched raw and zero-only controls use the same header, goal-directed leaf
policy, shared syntax table, and proof packet protocol. These controls were
created for this comparison. Their behavior on ignored proof payloads need not
match an older forward checker's accepted JSON language. The claim is equality
of the corresponding mathematical consequence relations, not byte-for-byte
or all-JSON trace identity with a different certificate interface.

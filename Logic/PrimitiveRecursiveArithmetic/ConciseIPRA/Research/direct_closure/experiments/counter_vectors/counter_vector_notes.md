# Counter-vector computation packets

## Status

This is an ancillary, exact-theory certificate tradeoff, not a new arithmetic
axiomatization and not an improvement of the 529-byte frontier. The standalone
checker is 533 normalized Python bytes, 271 significant tokens, 314 AST nodes,
and 336 bytes after gzip compression at level 9 with mtime 0. The baseline is
529 bytes, 266 tokens, 310 AST nodes, and 333 gzip bytes. Measurements use
CPython 3.12.14 and include imports, JSON input, every rule, and the verdict.

The gain is the removal of a normalization obligation: successor computation
at literal predecessor zero can be certified directly. The previous protocol
requires replacing that predecessor by a syntactically nonzero term known to
equal zero. Literal-zero initializers still require the inherited repair.

## Exact change

Only the computation branch changes. A packet remains `[m,s,u,t]`. For a
computation packet, `m=[]`, `u` is the initializer and is truthy, and `t` is
the update. The source field `s` is now a vector:

- `s=[]` selects the zero computation;
- `s=[n]` selects successor computation with predecessor `n`, including `n=0`.

Additional vector entries are ignored annotations. The generated equation is

```python
[[s[:1] or 0, u, t], i(t, [s[0], u, t], 3) if s else u]
```

The source counter is therefore exactly scalar zero for the empty vector,
and a unary successor for a nonempty vector. The equation and all surrounding
scope validation remain the inherited neutral-scope protocol.

The complete checker imports no producer, normalizer, measurement code,
mathematical library, or table of theorems. The proof data are parsed by JSON;
they are never evaluated as Python. Acceptance is exit status zero together
with exactly `ACCEPT\n`. Exceptions reject.

## Soundness

Retain the sorted decoder and opening lemma of
`neutral_scope/reference/inherited_arity_checker.tex`, and the local-scope
and neutral-major proof of `neutral_scope/report.tex`, at repository commit
`b17dd5487f34adea473a0204c5320fb3eeb8910e`.

All non-computation transitions are unchanged. In a successful computation
with a nonempty list `s`, the left counter is literally `[s[0]]`. The right
side opens the update at exactly `[s[0],u,t]`, so the existing constructed
computation argument applies, now without requiring `s[0]` itself to be
truthy. If the update uses the state, opening checks the recursive source at
numerical root depth 3. If it ignores the state, the usual constant-update
case applies. Surplus vector entries are absent from both expressions and
thus cannot contribute assumptions, parameters, or predicates.

For an empty list, the left counter is scalar 0 and the right side is the
initializer, exactly the base computation. An empty JSON string also selects
this same base equation; its meaning is therefore harmless. A nonempty JSON
string has a nonempty string slice as the proposed counter, and mandatory
opening of the generated equation rejects its ordered comparison at a
numerical position. The remaining JSON scalar types do not support slicing;
objects reject at the slice operation. Thus no new accepted raw case can
turn an arbitrary numerical counter into an unsupported successor.

The generated assumption may contain freshly admitted parameters. As in the
inherited proof, soundness only needs its simultaneous zero instance: it is
an I0 or IS instance. The retained goal and context do not contain these new
parameters. Substitute all of them by zero in the continuation and cut the
proved computation instance. This is the inherited zero-instance discharge
argument, not a claim that every raw generated assumption is uniformly true.

Induction on finite successful execution trees, using the unchanged
hypothesis, transport, closure, paired elimination, and introduction cases,
therefore proves soundness for the same native calculus.

## Completeness

Every canonical old computation packet has source field `n` when `n` is
truthy, and source field 0 for the base. Replace its source by `[n]` in the
former case and `[]` in the latter. For these old packets the generated raw
equation is identical, including the scalar-zero spelling of the base
counter. All other packet fields and all object formulas are unchanged.
This gives an exact execution simulation for canonical certificates.

The established compiler of native proofs into the old protocol therefore
also compiles into the new one. Conversely, soundness maps every accepted
new certificate to the same native theory. Both numerical interpretations
are the identity; equivalence and equiconsistency with iPRA are inherited.

For the improved producer one can omit predecessor-zero repair. Only the
initializer restriction remains. With

    C = I(S(S0),S0;v.0),

the direct computation `C=0` permits replacement of a literal-zero
initializer by C, followed by equality transport. A zero predecessor does
not need replacement because `[0]` is a nonempty source vector.

## Direct certificate

`direct_successor_zero_identity.json` is one instruction proving

    I(S0,S0;v.v) = I(0,S0;v.v).

Its source vector is `[0]`. The inherited 529-byte protocol cannot directly
select successor computation at literal predecessor zero: a zero source
selects its base branch. The inherited three-node certified-zero
normalization is no longer needed for this computation.

## Validation

`verify_counter_vectors.py` compares the old and new complete executables
under ordinary Python and `python -O`, using 46 inherited local-scope cases.
They include real equation induction, compound cases, transport under Q,
nonvacuous D elimination, out-of-scope variables, forbidden compound
progress, false scalar majors, and malformed packets. Six further controls
exercise the changed source interface. The result is 300 CLI checks, zero
mismatches. These are finite regression checks; the soundness and
completeness claims rest on the proof above and the cited inherited lemmas.

## Rejected 528-byte candidate

Deleting `or 0` saves five bytes but changes the base counter from scalar 0
to the empty-array zero alias. The raw certificate then fails to prove the
canonical base example, despite both spellings decoding semantically as zero.
The inherited decoder theorem explicitly does not assert interchangeability
of arbitrary raw aliases. We have not proved an alias-conversion theorem for
this variant. The 528-byte candidate is therefore excluded from all complete
checker claims; the receipt records the failed canonical-base test.

## Source attribution

The baseline checker and untrusted test support are copied from Vladimir
Reshetnikov's ProveIt, under its MIT-0 license, at the commit given above.
Relevant paths below `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research`:

- `neutral_scope/code/checker.py`
- `neutral_scope/code/readable_checker.py`
- `coverage_and_kernel/tests/producer.py`
- `coverage_and_kernel/tests/protocol.py`
- `coverage_and_kernel/tests/build_cases.py`
- `coverage_and_kernel/tests/inherited_verify.py`

The counter-vector branch and this comparison are the changes in this
ancillary experiment. They do not establish any absolute minimum.

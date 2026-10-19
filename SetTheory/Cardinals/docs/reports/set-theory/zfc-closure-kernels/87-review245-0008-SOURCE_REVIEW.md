# Source review of the released independent runtime checker

This mathematical review applies to the final portable engine and helper identified in the release section below. Earlier implementation-only caveats have been resolved by explicit input guards, the zero-count strip correction, and assertion-safe execution. Full input binding and source bisimulation remain separate checks.

## Assessment

No mathematical soundness blocker was found for the exact 245-state table and
the independently bound 6,460-site input. A successful full run supplies
fresh executable ordinary-mathematical verification of the stated universal
instruction contracts. It is not a Lean/Rocq kernel verification.

## Soundness of the steps

1. The zipper has an explicit orientation. Its literal step correctly moves
   the read cell to the opposite side when continuing in the same direction,
   and restores the written cell then switches orientation on reversal.
   The explicit accumulated motion is checked against the target head shift.
2. Affine run lengths have nonnegative constant and coefficients. A
   non-self-loop can consume a run only if its constant is at least one;
   it therefore never assumes an unproved zero/positive branch of a variable.
3. A same-state, same-direction self-loop consumes a whole natural-length
   run by induction on its length, writing exactly the indicated homogeneous
   replacement. The accumulated duration and motion are exact affine terms.
4. Each of four block-traversal schemas is independently replayed on the
   actual table with an arbitrary natural block value and opaque arbitrary
   contexts on both sides. Each returns to the same state/orientation and
   has duration exactly `v+2`, the encoded block width. Structural induction
   therefore lifts it to every finite block list, including the empty list.
   The opaque tail's width variable is interpreted as `sum(v+2)` for its
   actual values. It is not a finite sampled tail or a premise restricting
   the tail to a given length.
5. Normalization uses exact word identities and absorption of finite zero
   suffixes into the infinite zero exterior. The general identity
   `C(A)1 = 1B(A)` follows from empty/cons induction: the base is `1=1`, and
   `C(v)1=1B(v)` gives
   `C(A)C(v)1=C(A)1B(v)=1B(A)B(v)`. Reversing proves the second rule.
   The program checks the empty/one-block algebra, while this human-reviewed
   induction supplies its general list justification.

## Quantification and endpoint

Affine slots are: constant0, gap1, independent logical registers2–10,
arbitrary first spare11, and width of the arbitrary remaining spare list12.
Each zero-decrement sets only its selected register to zero. Each positive
branch substitutes one plus that register's arbitrary natural variable.
All other registers remain independent. A first arbitrary spare followed by
an arbitrary finite tail represents exactly all nonempty finite spare lists.

Successful nonhalting cases compare the entire symbolic tape, state and
orientation against the exact target, and separately compare absolute head
motion with minus overflow. They require strictly positive finite duration.
Halting cases must reach the actual old-label halt254. The 4,000-symbolic-step
limit bounds proof construction; exhaustion fails the obligation rather than
assuming a bound on actual machine time or register values.

## Final portable release and completed-result review

The final source diff was independently reviewed on 2026-10-18. Changes add
explicit table/domain/complete-trie guards, preserve the ordered source
operations against a pinned baseline, record checker/helper identities, and
correct `strip(pointer, bit, 0)` to return the original pointer. The symbolic
execution engine is unchanged. The current guarded source conservatively
requires positive break/continue counts, as used by these exact inputs.

Final hashes:

- Checker: `afb9fd0d070f5b2c4b1c951f36eb11cf60f0b94c1bff893793ccbad2ee0033b8`
- Helper: `0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346`
- Old-label table: `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`
- Logical sites: `f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745`
- Final summary: `ffda08405dd1e079f932860937d145a7c5cec139406228c8c1eea63e529e1afb`
- Per-case data: `2d5ad18d1b23e15dba8022ca6ad3b6b5ee846e0b42c25abd03c44aeb8712bc85`

The final summary reports `UNIVERSAL_MATHEMATICAL_PASS` after 176.198 seconds.
I independently checked its data against the files and verified:

- Exactly all 8,391 expected named guards, in exact order, with no omitted case
- Exactly 2,312,645 symbolic rules
- All 490 actual transition rows appear in the directly used row set
- Every duration has 13 affine components, all nonnegative, and a positive
  constant; minimum constant 13
- The recorded checker, helper, table and site hashes match the actual files

The input guard now checks a complete prefix-free binary tree of 6,460 leaves,
depth at most 64, valid logical operands, and exact ordered instruction
operations. Its tree has depth 51. The separate source-bisimulation check remains
necessary: equal ordered instructions alone do not prove control equivalence.

The final release was separately reviewed against the previously guarded
source. Its only changes are an explicit non-assert optimization rejection
before importing the helper, recording execution/environment flags, portable
input/output path selection, and a clarifying affine-variable comment. No
mathematical proof-kernel changes were made.

The helper selects input and output paths from `B245_INPUTS` and `B245_OUTPUT`,
or defaults to `inputs` and `results` next to the package's `code` directory.
These paths select inert input data and result destinations; the pinned baseline
site hash remains checked. Packaged `code/symbolic_runtime.py` and
`code/independent_runtime.py` were verified byte-for-byte against these reviewed
release files.

The completed `baseline245_portable_release_universal_summary.json` embeds
optimization 0, `__debug__=True`, bytecode writing disabled, and no
`PYTHONOPTIMIZE` value. The in-engine guard raises `RuntimeError` if assertions
are disabled, independent of Python's `assert` statements. This supersedes
the earlier post-run-only assertion provenance and does not require the
separate wrapper. The per-case proof data is identical to the prior guarded
release, as both parsed JSON and SHA-256 identity.

**Final receipt:** the reviewed source and completed data support fresh
universal ordinary-mathematical verification of all 8,391 instruction cases
for this exact 245-state table. No remaining source-review blocker was found.
This does not upgrade the result to a formal Lean endpoint or PA proof, and
does not certify any proposed 244-state table.

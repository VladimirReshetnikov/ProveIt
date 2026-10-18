# Forward carry with 244 states: universal arithmetic, incomplete conditional behavior

Starting from the pinned Context246 table, change:

```text
255/0 = 1 L 63
255/1 = 0 R 95
```

Delete states 112 and 131, whose incoming edges are now absent. The resulting
full table has 244 working states, but is **not a certified consistency machine**.

For `B(v)=0 1^(v+1)`, a marked file is `B(A) 00 1^x B(S)`, with nonempty `S`.
`prove_forward_carry.py` reuses only the baseline's explicit literal,
unary-induction, finite-list-induction, and word-identity proof rules to
establish:

- Positive decrement: unchanged output, exit in state 48 at head 0,
  `2 width(A)+4` steps.
- Increment: unchanged output and an appended spare of value 1, exit in state 48 at head -1,
  `2 width(file)+7` steps.
- Zero: unchanged values, shifted right by 1, an appended spare of value 1,
  exit in state 48 at head 0,
  `2 width(file)+6` steps.

The proofs quantify over all allowed finite lists and values, arbitrary
left exterior, and blank right exterior. They do not use bounded examples
as induction premises. They are ordinary checked mathematical arguments,
not Lean/Rocq kernel proofs.

## The exact collision

Selected zero with suffix `S` and selected one with suffix `S+[1]` both reach
exactly state 48, head 0, tape `left 1 B(A+[0]+S+[1]) blank`. Their elapsed
times differ, but elapsed time is absent from a machine configuration.
A common deterministic return rule cannot recover the original branch.

This does not by itself rule out an existential simulation that chooses
different stopping times: one future run could visit two different frames.
It also does not prove both inputs arise on the unique blank run, or give
a general state-count lower bound. A stronger count/phase invariant or an
earlier preserved flag could change the design.

The literal simulator checks three witnesses, including nine primaries
with all spares equal to 1. Merely restricting spare values to 1 leaves the
collision intact. The complete intermediate configurations are in
`collision.json`.

From the archive root:

```sh
export ZFC246_BASE="$PWD/baseline/context246"
python3 experiments/forward/prove_forward_carry.py
python3 experiments/forward/check_collision.py
```

Both scripts write results beside themselves. The root `verify.py` wrapper
instead replays them in a temporary copy and leaves the release unchanged.

# Conditional rank phase from an origin digit and four blocks

[`Model69Phase.lean`](Model69Phase.lean) proves three elementary cut lemmas in
arbitrary `IΣ₁` models. If `modulus=4*n` and `C%modulus=1`, then
`(C-1)%4=0`. If `q%4=0`, `A%4=0`, `M%4=3` and

```
R=A+M+q*D+q*q*E+q*q*q*H,
```

then `R%4=3`. The third theorem composes the two statements with `A=C-1`.
It obtains the predecessor residue using an explicit quotient, so no hidden
assumption that natural subtraction is integer subtraction is needed.

This is a **conditional model cut**, not yet the rank phase of the actual
positive 2011 Carrier65 zero. The specific low digit `C%modulus=1`, the
factor-of-four modulus, the whole four-block identity and the `q`/`M` residues
must still be derived from that zero's window, repunit and exact mask data.
No conclusion here identifies the separate phase-split2471 tuple or proves a
69-operation converse, graph bridge, fixed-port calibration, or iPRA theorem.

## Paired replay and failed attempt

[`replay.py`](replay.py) compiles this source on both sides of the
[independently audited 70-source parent](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md),
checks source and direct imports, and reruns the parent comparator before and
after. Session 74044 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_PARENT_PHASE 27d4b04962f44768e70fcb4bd2faa74935e0044eb2965776c016c4b79b6d6d9f`.
The [receipt](replay-receipt.json) records two successful Lean exits and
matching objects; the [terminal observation](terminal-observation.json)
records the actual outer exit. All three axiom reports list `[propext,
Classical.choice, Quot.sound]`, with no warnings or `sorryAx`. An independent
audit of this suffix is pending. Lean metatheory axioms are not axioms of
object-level iPRA. The package-transitive/dynamic ancestry and original
Foundation wrapper exit retain the parent audit's qualifications.

The first exploratory compile, session 7851, actually exited 1: it rewrote
the modulus before rewriting the origin equation, leaving a failed goal and
`sorryAx` in the unfinished theorems. Reversing the rewrite order fixed the
problem; exploratory session 78622 actually exited 0 with no warnings. Only
the corrected source was used for the paired run above.

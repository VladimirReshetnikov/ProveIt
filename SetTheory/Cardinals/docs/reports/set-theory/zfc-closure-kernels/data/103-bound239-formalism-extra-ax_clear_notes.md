# Experimental AX clear-top protocol and its measured rejection

This is a source-calculus proposal. It has no validated smaller binary machine.

## Register-level identity

Use the actual dual Cantor pairing `P(a,b)=tri(a+b)+b`, formula constructor
`Imp(a,b)=4P(a,b)`, and native DROP/MP/NIP behavior. The four relevant fields
are `(t,h,w,a)` = `(top,cache,theorem_stack,additive_parameter)`. Give every
inserted command additive input 0.

For all natural inputs, the command prelude

```
DROP; DROP; MP(added parameter 0); NIP
```

followed by one extra NIP exactly when `h=a=0` ends at

```
(0, h, P(t,w), a).
```

Indeed after two DROPs the top and cache both equal `h`, and the stack is
`P(h,P(t,w))`. MP fails unless `4P(h,a)=h`. If `h+a>0`, then
`P(h,a) >= h+a >= h`, with strictness after multiplication by four whenever
`h>0`, while `h=0<a` also gives strictness. Thus the equality holds exactly
at `(h,a)=(0,0)`.

In the ordinary case MP clears top and cache without pushing, and NIP pops
`h`, leaving `P(t,w)`. In the exceptional case MP successfully pushes one
extra zero; the two NIPs remove that zero and the original zero cache.
Every NIP starts with cache 0, so the native pre-read halt test never fires
inside the prelude, even when the original cache was 1.

## Why the proposed altered AX can preserve refutability

The old AX first pushes the previous current theorem, clears the current
register, and then emits GEN and the eight logical rows before the theory
bundle. Change only that *initial* push into a clear of the old current
register. The later internal PUSH operations used to build formulas remain.

Soundness survives because the altered operation removes an already valid
theorem from the retained stack and emits exactly the same valid new rows.
An old AX can be simulated by the prelude above followed by the altered AX:
the old current theorem is already backed up, the current register is zero,
and all other relevant fields are restored. The special prelude choice is
computable from the register state. One must still give the actual finite
proof-word translation and fair enumeration argument to turn this into a
theorem for the fixed unbounded source program.

## Concrete source-DAG cost

The tested baseline comes from the exact 240 source in this session.
Node 56 is the 19-leaf initial PUSH, and node 197 is the existing two-leaf
clear of register 1, `(CD1,CC1)`. Replacing only the first AX occurrence
at original path `111010010010000` preserves all other PUSH occurrences.

* Original source: 225 distinct source-DAG nodes, 6,455 leaves, maximum
  zero run 6. Modified source: **227 nodes**, 6,438 leaves, zero run 6.
* Parent's best closed-reassociation source: 224 nodes, 6,455 leaves,
  one remaining zero run 7. Replacing its first AX PUSH at
  `1110100100100000` gives **227 nodes**, 6,438 leaves, zero run 6.

The gain in leaf length loses sharing. These are DAG counts including
leaf kinds, not final binary working-state counts. Furthermore the existing
binary context folds are not automatically valid under reassociation: the
parent's independent actual-table test found failures beyond the long-zero
paths. Thus this control is rejected as a present sub-240 construction.

The companion `ax_clear_protocol.py` tests the exact prelude with native
halting checks; no state-count result is inferred from the finite tests.

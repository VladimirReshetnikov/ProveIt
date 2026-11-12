# Bounded two-gate screen for 13/86/99

The checker pins the [13-natural-input, 86-operation graph](../ordinary13-natural-forced-w86/)
and examines every gate whose output has exactly one distinct graph consumer.
For each such predecessor/consumer cut, it enumerates a replacement of the
consumer by **one** binary `+`, `-` or `*` gate whose operands are available
before the original consumer: any input, port, earlier node other than the
removed predecessor, or literal 0 through 4. The removed node cannot be used
by another node by construction. This finite family covers 59 cuts and
1,118,628 ordered replacement gates.

Six reproducible pseudorandom assignments of all 13 inputs and four ports are
evaluated modulo 1,000,000,007, using seed 947521. No candidate matches its
original consumer at all six assignments. Each rejection has a concrete
modular counterexample, so no survivor is an all-port, all-input polynomial
identity in this explicitly enumerated family. The checker enumerates zero
operands directly rather than assuming modular invertibility.

This is **not** a global operation lower bound. It does not cover identities
that hold only at the fixed compact ports, replacements with additional gates
or new constants, simultaneous edits outside one cut, changes of witnesses,
conditional equalities at zeros, or different zero-equivalent polynomials.
It does not establish any degree, iPRA endpoint, or provider claim.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural86-two-gate-screen/check.py | cmp - research/ordinary13-natural86-two-gate-screen/result.json
```

The output in [result.json](result.json) is deterministic. No Lean process is
run.

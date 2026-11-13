# Trace75 positive K register

`Trace75Kpos.graph_K_positive` is Lean checked in every `IΣ₁` model. At
arbitrary natural ports with beta positive and ten positive witnesses whose
Lean trace75 ring value is zero, it proves the actual signed K register is
positive in the model's difference ring:

```
K = X*(3*c-2*X)+2 > 0.
```

It first derives `X<c` from the unscaled first-index bound, then casts the
positive gap into the difference ring. This is one premise of the K7 carrier
argument; it does not by itself establish nonnegative transport, a trace74
guard, halting, iPRA or file/payload binding.

Accepted source `Trace75Kpos.lean` SHA-256
`58984eb7a1d8f12a0fa6685c63c3d8c8897b4b968dab0328c53bed30a7c6937c`;
`run-kpos-v2.py` accepted `observations/kpos-attempt02/`, object
`/tmp/trace75-kpos-rq1vg901/Trace75Kpos.olean` SHA-256
`c9dcda78a63d32accfcd4efc52e19f8e69747cc704c26f5fbdbd29e2eb9aa7d6`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. The first
attempt failed before elaboration on a missing transitive path and is retained.
Selected direct and several nearby transitive providers are pinned; full
project/package transitive, historical source/object and dynamic ancestry
remain inherited.

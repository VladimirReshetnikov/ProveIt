# Trace75 nonnegative transport and positive old mask

`Trace75Transport.graph_transport_and_mask` is Lean checked in every `IΣ₁`
model. For arbitrary natural ports with beta positive and ten positive
witnesses whose Lean trace75 ring value is zero, it proves

```
0 ≤ B,    F + alpha < q.
```

Here B is the actual signed trace75 transport register in the model's
difference ring; `F` and `alpha` are witness slots 1 and 2, and the inequality
is in the natural model. The proof uses one common `tau,f0,V0,Z0,y` tuple from
the actual carrier bound, chooses a sign for its Z representative, and
combines the signed-carrier and offset inequalities with positivity of the
actual h,H,D,K and input n. It uses the exact carrier identity with `D=XY`,
then derives positive C from B≥0. All these refer to the same p and v.

This establishes the old trace75 chart's mask guard. It does **not** establish
`F+C<q` for arbitrary positive zeros of the new trace74 chart, so it is not
an unguarded 74/75 equivalence. It also does not establish a machine halt or
iPRA theorem, fixed-port specialization, or Lean binding of JSON/payloads.

Accepted source `Trace75Transport.lean` SHA-256
`738ffa3484f6a24c6e221629b6d49950185a909404ef2e84fbd16583b27ddf6f`;
`run-transport.py` accepted `observations/transport-attempt01/`, object
`/tmp/trace75-transport-iiurih17/Trace75Transport.olean` SHA-256
`c660d042eaa9e9e525d7bb0d09ca03651f2ec9b702a93f5bbd48da0e3c5ade54`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct and several nearby providers are pinned; project/package
transitive, historical source/object, generic rebuild between-stage stability,
and dynamic ancestry remain inherited, without a complete closure scan or an
independent replay.

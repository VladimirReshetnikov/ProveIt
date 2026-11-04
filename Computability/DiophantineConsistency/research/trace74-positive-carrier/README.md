# Positive carrier coordinate under a signed offset hypothesis

`Trace74PositiveCarrier.exists_positive_carrier` works in an arbitrary IΣ₁
model. If a signed difference-ring constant `C-G` is `M*(P-N)` and
`P < Q*Q*B + N + tau*phi*y`, it constructs a strictly positive internal
coordinate `v7` satisfying

`M*(v7-Q*Q*B)+(C-G)=M*tau*phi*y`.

The quotient is represented by positive and negative parts `P,N` in the same
model. The theorem does not establish the offset divisibility, the size bound,
the graph register bindings, the auxiliary Pell norm, or an actual graph zero.
It uses a captured provider chain, not a clean canonical rebuild.

Lean 4.32.0 session 88104 exited 0 with only the standard metatheory axioms
`[propext, Classical.choice, Quot.sound]`. The command was:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74PositiveCarrier.lean \
  -o /tmp/Trace74PositiveCarrier.olean
```

Source SHA-256 `cd2d36ee69d0d5f5bd2f9e2d35c562087f91aaa106eb37dd9c9ce92a40ed32f9`;
object SHA-256 `d8ead3b8fcbf48cad771f0af303f10eab156ce33a1f707e173b7beddb39dd092`.

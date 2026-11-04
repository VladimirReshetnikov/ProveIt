# Deriving the dynamic chart bindings

`Trace74StaticBindings.bindings_from_static` constructs the explicit `hbind`
callback of `Trace74WitnessAssembly` from simpler hypotheses on the same
10-coordinate tuple. Positivity of the eight unchanged coordinates, together
with the constructed positive T and carrier, gives positivity of the entire
tuple. The chart's Q, E, F and M must have the specified static values; the
V and Z registers must have the displayed forms in T and the carrier. The
theorem then derives the dynamic V and Z equalities from the T and carrier
equations, including the same quotient and ordinate from the selected orbit.

These static identities, positivity assumptions, signed offset divisibility,
fixed-port CRT and the other seed premises are **not** proved by this packet.
In particular this does not yet produce an unconditional graph zero. The
module uses the same captured-provider import chain as the witness assembly.

Lean 4.32.0 session 39885 exited 0 without warnings; `#print axioms` gave
`[propext, Classical.choice, Quot.sound]`:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74StaticBindings.lean \
  -o /tmp/Trace74StaticBindings.olean
```

Source SHA-256 `ce3224d5cf9a15445b949a29cc4000b82d4d6cd2246b55c783146494d44944a3`;
object SHA-256 `9adc576b9b5ebd5cc7be0a1ec80c4f7407df98019d917cf958de25e267abb632`.

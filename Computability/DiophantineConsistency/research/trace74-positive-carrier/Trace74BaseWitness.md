# Positive graph witness from fixed base-register identities

`Trace74DynamicBindings.dynamic_forms_from_base` derives the two dynamic
binding conditions from the actual graph's V/Z formulas, requiring only fixed
base values for the components c, rank, trace coefficient f, B, signed
offset and the chart M register. It proves the components are unaffected by
updating the T and carrier coordinates.

`Trace74BaseWitness.exists_positive_zero_from_base` composes this result with
the previously checked static and Pell-orbit construction. It constructs one
strictly positive 10-coordinate zero of `Trace74Mask.value74` from explicit
assumptions on one base tuple: positivity away from the two updated positions,
base Q/E/F/M and component c/rank/f/B/offset identities, the Pell seed and
index relations, positive B, and signed offset divisibility. It does not assume
the former universal `hbind` callback or either dynamic chart form.

The required base identities, candidate positivity, signed divisibility,
fixed-port CRT and seed conditions have not been established for the actual
candidate in Lean. This theorem is therefore conditional and does not yet
produce an unconditional graph zero. Its imported modules are captured
providers, not a clean rebuild of the full current source tree.

Lean 4.32.0 compiled `Trace74DynamicBindings` in session 29196 and
`Trace74BaseWitness` in session 5053; both exited 0 with no warnings and
reported only `[propext, Classical.choice, Quot.sound]`. The following command
was run in that order with `NAME` set to each module name:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/NAME.lean -o /tmp/NAME.olean
```

```text
source Trace74DynamicBindings  03d9c137b1758484e8422ffb633a8322ce5b0b400b64aa9372dcffb6bb6a7f3a
object Trace74DynamicBindings  0461d05fb4c6155d1d9635e182e4a1f221717ad8b80c7d95e22f5dd84621b3f8
source Trace74BaseWitness      862342078e01e6692a3afd22402ebaae27db1e7471a8f0108830875b8b97e476
object Trace74BaseWitness      5f8d8adadd4e2f55cc9b31717b37cba779b8f92e7e728fb79a824e3d571e8246
```

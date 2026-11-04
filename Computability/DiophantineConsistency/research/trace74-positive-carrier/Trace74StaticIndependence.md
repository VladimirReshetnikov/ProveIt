# Static chart register independence

`Trace74StaticIndependence.static_independent` proves by definitional equality
that updating the T and carrier coordinates of the actual trace74 tuple does
not change chart registers Q, E, F or M. `static_from_base` reduces their four
universally quantified identities in `Trace74StaticBindings` to identities
checked once on the base tuple.

The four base identities and the two dynamic V/Z forms are still assumptions;
the theorem does not establish the fixed-port candidate or a graph zero. It
uses the captured-provider chain documented by the other carrier packets.

Lean 4.32.0 session 98475 exited 0 without warnings; `#print axioms` gave
`[propext, Classical.choice, Quot.sound]`. The command was:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74StaticIndependence.lean \
  -o /tmp/Trace74StaticIndependence.olean
```

Source SHA-256 `0ef0c5fb84a09ee24a3b35dcb2d4d67eb91a390278192fd3e4d604148fcfabba`;
object SHA-256 `0f2329952124a15e066029d9e5ffb992979c708ccca2b631078b093ac4f8afd5`.

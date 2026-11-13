# Trace75 signed carrier magnitude bound

`Trace75CarrierBound.graph_carrier_bound` is Lean checked in every `IΣ₁`
model, at arbitrary natural ports with beta positive and any positive trace75
zero in the model's difference ring. It returns **one coherent tuple** of
positive `tau,f0,V0,y` and natural `Z0` such that the actual signed V and Z
register squares are the embeddings of `V0²` and `Z0²`, respectively,
`Z0=(M*tau*f0)*y`, and

```
2*(tau*f0*y) < V0².
```

The proof uses the actual trace75 unsquared-trace signed residue and existing
generic adjacent-Pell and size lemmas. This is the first signed carrier
estimate, not yet transport nonnegativity `B≥0`, positivity of the mask C,
halting, an iPRA theorem, a trace74 guard, or a Lean file/payload binding.

Accepted source `Trace75CarrierBound.lean` SHA-256
`57e471794f91cb8dc9cb85c28f0e921cadac48b064c862578f02729d7f06d2b3`;
`run-carrierbound.py` accepted `observations/carrierbound-attempt01/`, object
`/tmp/trace75-carrierbound-dztlf9a0/Trace75CarrierBound.olean` SHA-256
`8ef47fc9a296744657c3f3dfd7130aeab24058371533a995a247e045318af923`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers and nearby adjacent dependencies are pinned;
project/package transitive, historical source/object and dynamic ancestry
remain inherited, without a full closure audit or independent replay.

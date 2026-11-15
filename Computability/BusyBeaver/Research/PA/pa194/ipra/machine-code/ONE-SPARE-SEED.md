# Connection to the startup suffix

`PA194OneSpareSeed2.fileRepeat` proves for every standard natural number n,
in every PRA model, that the established n-block file-code expression for n
one-valued blocks and a zero tail equals `repeatOutput(modelNumeral n, 0)`.
The proof uses an external induction on standard n. The model-length carry and
return theorem separately uses internal open induction and therefore permits
nonstandard counts.

`modelSeed` applies this identity to the previously verified startup data to
show `repeatOutput(modelNumeral 25, 0) = modelNumeral seedTail`.
`PA194OneSpareSeed26.modelSeed26` adds one block and proves the exact suffix
used by the current site-29 step:

```
repeatOutput(modelNumeral 26, 0) = block(1, modelNumeral seedTail).
```

All these equalities hold in every PRA model. They identify the input of the
model-length file round trip, but do not by themselves generalize the complete
site-29 source step or prove the consistency equivalence.

Run `check-one-spare-seed.sh` with the arguments documented by its usage; the
`ROUNDTRIP_STAGE` is the output of the successful
`check-one-spare-file-roundtrip.sh` replay. The checker rebuilds the earlier
seed-data source and the 25-block identity, checks their axiom reports, and
pins and audits retained object inputs. `PA194OneSpareSeed26` also passed a fresh source rebuild with the same
coherent roundtrip, site28 and site27 object roots; the independent
hash-auditing wrapper including that corollary has passed. This incremental check does not rebuild the
transitive source closure of its staged inputs.

`PA194SeedFileRoundTrip.roundTrip` composes `modelSeed26` with the full
model-length roundtrip at count 26. It starts from the exact suffix
`block(1, modelNumeral seedTail)` and returns the named `repeatOutput` file
with successor count 27, arbitrary model-valued spare and odd marker, and the
exact nested clock. A fresh rebuild against the coherent roundtrip and seed
stages has passed. The expanded `check-one-spare-seed26.sh` replays and audits
all four sources, including this composition; its hash-auditing replay passed in `/tmp/pa194-one-spare-seed26-check.log`.

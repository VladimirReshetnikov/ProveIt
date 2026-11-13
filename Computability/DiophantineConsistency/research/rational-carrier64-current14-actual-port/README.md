# Combined actual-port client: retained resource failure

This initial client tried to import the rational specialization and the
matrix-free structured-port endpoint together, prove fixed beta nonzero,
and state separately the external rational zero equivalence and the
existing integer-language iPRA theorem. It did **not** pass: attempt01
terminated with Lean exit −6 at the `-M2400` interpreter memory limit,
without an output object or theorem reports. The guard itself did not
stop the run; direct inputs remained stable. The run took 2.266 seconds,
with peak sampled group RSS 2,524,778,496 bytes under the 3.5 GiB limit
and available memory above its 10 GiB floor.

This is a resource failure, not evidence for or against the mathematical
claims. The source is unchecked. A separately checked beta proof and
actual-port external equivalence are retained in the sibling
`rational-carrier64-current14-actual-port-split` and
`rational-carrier64-current14-actual-external` packets. Neither creates
a rational-leaf iPRA object-language sentence.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64ActualPort.lean` | `10e84da73a7b7a6c7b2b74f952df0466067e1220372a11b9dfe6408b214d82ab` |
| `check01.py` | `9e1081fd65879bce4765f5151bbc276400dd421a0f0f9ef6924e175c7bc44e74` |
| `observations/attempt01/compile.log` | `48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a` |
| `observations/attempt01/result.json` | `64a10581613797cc1f7c8a74c186889e42c88beff69627d8ae7d29be9c8f61d1` |

# Independent guarded replay of the 81-operation zero-existence theorem

On 2026-11-04 the independently prepared [`run.py`](run.py) replayed the
existing `P64QCubeExistence.lean` source. Lean exited 0 in 7.191 seconds;
the retained [`compile.log`](observations/attempt01/compile.log) reports
exactly the four expected declarations and only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`, warning, or error.
The machine-readable [`result.json`](observations/attempt01/result.json)
records the command, search path, exit, and hashes. The output object's
SHA-256 is `74ef2f50d92729ca37cea7aaa5ea1d21df54eeaa6314aeb0fe5138818f23b8f2`,
the same as the object recorded in the original theorem packet and used by
the separately checked endpoint client.

The runner guarded the source, Lean executable, and the two direct input
objects by hash before and after the run, and checked that the search path
selected those two objects at both observations. It refused pre-existing
output directories. The output file is separate from the original object.
This is an independent execution and receipt over the **same captured
providers**, not a fresh source build or an independent authentication of
transitive project objects, external packages, dynamic libraries, or the
entire search path. The check covers the all-model positive-zero existence
equivalence; it does not itself establish the iPRA endpoint or bind the
symbolic graph and coefficients to JSON, gzip, TeX, or PDF semantics.

The runner contains fixed workspace and `/tmp` paths and refuses to overwrite
the recorded directories. With those captured inputs still available, a
separate reproduction requires choosing fresh output and observation paths
in a copy of the runner. Its original runner SHA-256 is
`bcf14f9d041ce8cea25bc84c348cb9eb976b0191decd04677770bf9bfe66722b`.

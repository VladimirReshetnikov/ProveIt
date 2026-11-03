# QM40 incremental retry stopped during dependency resolution

The first incremental retry, tool session `42ee25`, exited 1 before invoking
Lean elaboration. Its fresh library contained an empty `DiophantineConsistency`
directory. `lean --deps` reported the fresh-library path for
`AdaptiveQM40Model.olean`, even though that file was absent there; the driver
rejected the missing direct input. The retained `failure.json` and
`preflight.json` are the actual output files from
`/tmp/ipra-qm40-incremental-author-20261102-c`. No native theorem, checks
theorem, or output object was established by this attempt.

The failing driver was commit `d7df339ed4` with SHA-256
`31896a24ac4a114d18b344e010c7c28f13ac6a5d41f4f902fde204f101513958`.
The [corrected retry](../../research/adaptive-qm40-native-incremental-retry/README.md)
creates a separate symlink overlay of the entire seed before asking Lean to
resolve project modules. That later driver still requires an actual bounded
run; this observation does not establish its success. The six inherited model
objects and all original ancestry limitations remain as in the
[earlier timeout record](../adaptive-qm40-native-bounded-replay/README.md).

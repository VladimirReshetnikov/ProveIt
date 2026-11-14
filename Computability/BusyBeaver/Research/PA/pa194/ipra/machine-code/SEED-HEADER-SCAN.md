# Concrete PA194 seed header scan

`PA194SeedHeaderScan.modelSeedAt15` follows the checked blank startup and the
12-step source-header prefix with the existing model-uniform state-84 scan.
After 58,209 steps it gives the exact state-15 tape halves in every candidate
PRA model. The complete encoded seed file, including all spare blocks, is
retained in the displayed output; no register value is approximated or
truncated.

This concrete-time endpoint is an intermediate point in the first seeded source
instruction. The more general `sourceHeaderTo17` theorem subsumes the remaining
scan and return for arbitrary model-valued header lengths and source files, but
it does not by itself name this exact 58,209-step state-15 checkpoint. Neither
theorem proves a complete arbitrary model-length source instruction or either
PA consistency implication.

`check-seed-header-scan.sh` rebuilds the source-frame, header prefix and scan
modules, checks selected direct source/object hashes, and rejects `sorryAx`.
Its prerequisite overlays retain unrebuilt transitive objects; it is a suffix
check, not a full dependency-closure replay.

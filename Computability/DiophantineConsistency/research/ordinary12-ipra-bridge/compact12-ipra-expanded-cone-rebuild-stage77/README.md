# Expanded compact/iPRA rebuild: stages 77–79, stopped on warning

This bounded author batch resumed the corrected guarded 425-module merged-root
build after 76 stages, rechecking all earlier runners, both baselines, the
quarantined rejected stage-64 object, all 425 source hashes, selected original
and merged provider files, prior output/log hashes and direct dependency and
companion guards. The exact runner SHA-256 is
`aa1dda158d31d81669a6dd766b7a402b9fdd9d1803e2fb9596c1d9f0a6d2f4fa`.

Stages 77 (`CompositionModel`) and 78 (`KLowerSeed`) exited 0 without warnings;
their recorded direct source and dependency guards were unchanged. Stage 79
(`KLowerRaw`) exited 0 but warned that the section variable `hirr` was
unused in `raw_tagged`. The runner rejected the warning, marked stage 79
unsuccessful and exited 1; it did not reach its full post-batch overlay check
or stages 80–81. The rejected stage object SHA-256 is
`ca70aa5d67e2fdc4efef374b6071d4e5801046b2bc1cb863ebb43e5440dcca1c`
and must not be used as a successful import. The exact sources, dependencies,
logs and receipts are preserved under `observations/batch-016/`.

The warning is not a request to silently change the theorem's signature:
`include hirr` places it in scope, and existing `KLowerTag.lean` and
`KLowerQHyp.lean` pass `hirr` explicitly to `raw_tagged`. Removing the
parameter would require corresponding downstream changes. A separately
reviewed exact warning baseline or a signature-preserving correction and
fresh guarded retry are needed before resuming. This packet alone does not
establish a successful stage 79, iPRA endpoint, full ancestry audit or paired
replay.

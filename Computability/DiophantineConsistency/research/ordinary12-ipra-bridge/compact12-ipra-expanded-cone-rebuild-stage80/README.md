# Expanded compact/iPRA rebuild: stages 80–81, stopped on warning

This bounded author batch resumed the corrected guarded 425-module merged-root
build after stage 79's explicitly accepted exact warning. It rechecked all
prior runner hashes, both baselines and quarantines, all 425 source hashes,
selected original and merged provider files, prior output/log hashes and
direct dependency and companion guards. The exact runner SHA-256 is
`b0920ef9ee49036368ce79cd948f5136c9ec9808f64dde445068e28b593ff0d8`.

Stage 80 (`KLowerRel`) exited 0 without warnings; its direct source and
dependency guards were unchanged. Stage 81 (`KLowerTag`) exited 0 but warned
that section variables `hirr` and `ht` were unused in `tag_inhabited`. The
runner rejected this unbaselined warning and exited 1 before the full
post-batch overlay check and stages 82–84. The stage-81 object SHA-256
`48cf2bbd2d623aa105568704dc61b0ec1c073531e85d133a5df46e603d796829`
is rejected and must not be imported as a successful result. Exact source,
dependency lists, logs and receipts are preserved under
`observations/batch-016/stage-0080/` and `observations/batch-017/stage-0081/`.

The warning should not be addressed by silently changing the theorem's
signature: `include hs hirr ht` places these parameters in scope, and
`KLowerQHyp.lean` explicitly calls `tag_inhabited hs hirr ht`. A separately
reviewed exact warning baseline or a signature-preserving source correction
and fresh guarded retry are required before resuming. This packet does not
establish successful stage 81, an iPRA endpoint or a full ancestry audit.

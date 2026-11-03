# Expanded compact/iPRA rebuild: stages 82–84, stopped on warnings

This bounded author batch resumed the corrected guarded 425-module merged-root
build after stages 79 and 81 had separately accepted source-pinned exact
warnings. It rechecked prior runner hashes, baselines and quarantines, all
425 source hashes, selected original and merged provider files, prior
output/log hashes and direct dependency and companion guards. The exact
runner SHA-256 is
`971405d78d1a8869533e1adffcfb97ec2009edacef5c2364905bba8119521731`.

Stages 82 (`KQHyp`) and 83 (`KLowerEqv`) exited 0 without warnings; their
recorded direct source and dependency guards were unchanged. Stage 84
(`KQ1Model`) exited 0 but emitted three unused-variable warnings for explicit
`witness : V` binders in `member_left_congr`, `member_right_congr` and
`modelSetoid`. Its log also contains three named Lean metatheory axiom
reports. The runner rejected these unbaselined warnings and exited 1 before
the full post-batch overlay check and stages 85–86. The stage-84 object
SHA-256 `e52477f9a7fc2b6aae82a387281beb829246270cf7b3fbf6d3bdadb052077729`
is rejected and must not be imported as a successful result. Exact sources,
dependency lists, logs and receipts are preserved under
`observations/batch-017/stage-0082/` through `stage-0084/`.

The explicitly named parameters are threaded through other theorem and
domain definitions, so removing or renaming them should not be assumed to
preserve the named interface. A separately reviewed exact source-pinned
warning baseline or an independently checked interface-preserving source
correction and fresh guarded retry are required before resuming. This packet
does not establish successful stage 84, an iPRA endpoint or a full ancestry
audit.

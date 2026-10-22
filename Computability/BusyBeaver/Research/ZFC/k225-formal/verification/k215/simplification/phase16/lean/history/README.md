# Phase16 metadata history

The accepted packet is in the parent directory. Its capture and both saved reads
passed; owner and independent saved receipts are byte-identical. Raw process
records remain in [actual](../actual/) and [independent](../independent/).

The first capture failed before creating an archive because an exact pinned
phase15 archive was classified as new payload. Its source predecessor, raw error,
and failure record are retained inside the accepted archive. The packet's
`config.json` maps the source keys under
`/tmp/k215-phase16-publication/history/capture1-parent-archive/` to the archive's
`blobs/SHA256` members. The successor accepts only the eight hash-pinned parent
boundary files. This does not allow arbitrary nested archives.

The first saved read failed at a tuple/list comparison after validating its
inputs. The [entire prior captured packet](saved1-json-comparison/README.md), raw
error and failure record are retained here, separately from the accepted archive.
The successor compares canonical JSON representations. The independent invocation
was held until this repair and the owner's successful read.

These were metadata-packaging failures. No proof source or successful compiler
record changed. The earlier pre-mutation adoption-reader failure also remains in
the integration history and accepted archive with its original failed status.

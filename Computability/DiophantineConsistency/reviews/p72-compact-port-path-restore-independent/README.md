# Independent review: restored P72 compact port payloads

The current declared P13 and P14 paths resolve to the same four gzip files. This read-only checker independently verifies each against both pinned active-binding records and the source44 files, including compressed and raw SHA-256, raw length, minimal unsigned little-endian encoding and declared bit length. The binding marks MF already shifted; the checker does not shift it again.

The preserved `before.json` records the four target paths as absent before restoration, and the result binds that observation by hash. This reviewer cannot independently re-observe a past absence. The restored files match the recorded sources now; the script does not invoke the mutating restore operation. Neither the restoration nor this review is a Lean theorem about file or gzip semantics.

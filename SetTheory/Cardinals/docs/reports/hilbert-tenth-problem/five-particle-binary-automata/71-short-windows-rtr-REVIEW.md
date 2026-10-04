# Independent Report71 presentation and release-tool review

Disposition: **PASS**, 4 October 2026. This is a pre-seal functional review of the stable v3 article and its inspected release tools. The owner's final root-release seal and post-seal gate are separate and are not claimed here.

## Reviewed identity and execution boundary

All 944 lines of `release71.py`, `build_report71.py`, `selftest71.py`, and `provenance71.py` were read completely before execution, and their hashes were rechecked against the inspected bytes. The frozen input map is `ad643bd888c3a046c74d976d63c5753e65c3c72cbdf82ab7d6454c57483548e3`. The exact three adaptation diffs were independently reconstructed against the authenticated, unchanged Report70 release with manifest `0f96f8aa8bba3eb581070a3db48798ecba3ef0c49daa47a124e62b6754ee30e1`.

- Manuscript pins: `f0c4ebf30e03d9b1dbf09c5786649c07fda36c204f1f6480b78e19a4720d583b`
- Flattened source: `8d63dafe592cfb215f938fe4ac075f8e16dbe14c74d5d5c61b0b1abd030fa1e5`
- Final 13-page PDF: `0e88bb6899c39ba2a7991df468551cafef92730bcb66c00e91094e872b65d275`
- Dependency lock: `741c8b653fd8783c9afc29f8021a4a2c803140576cb0f6b1eb5ad39a9181e308`

All executions and generated outputs were confined to this reviewer's owned external workspace. The stable package was copied with file and directory metadata preserved, and the clone was independently compared to the original snapshot. Only inspected presentation/release tools, owned review scripts, standard byte/JSON/archive processing and TeX/PDF utilities were executed. Scientific source and audit helpers, scientific interpreters, CA or physical/trajectory simulators, schedules and Lean remained inert.

## Verified results

1. Input authentication and deterministic manuscript flattening passed. Frozen source and audit copies retain exact bytes, object sets, modes and nanosecond modification times.
2. Actual v3 and relocated actual v3 locked builds independently reproduced the exact packaged PDF. Each build created a fresh isolated format, disabled shell escape, retained the format recorder and all three TeX-pass recorders, authenticated the complete dependency union and selected maps, and produced the exact lock bytes. All 13 page PNGs were structurally and CRC/raster verified at 72 DPI; final layout/reference warning checks passed.
3. All 39 synthetic release-tool selftests passed. Coverage includes the deliberately first-pass-only `ifthen.sty` dependency, rejection when it is omitted, stale preflight input, invalid external pins, hostile temporary-directory environment variables, protected/aliased/existing outputs, symlink/hardlink/nonconforming inputs, source metadata changes, corrupt PNGs, manifest collisions, relocated rebuilds and archive traversal.
4. Two full test archives of the owned clone were byte-identical. Manifest authentication, exact inventory, sorted member order, fixed timestamp, Unix regular-file attributes, compression, CRC and every payload were checked. The authenticated extractor was verified independently against the manifest for the exact descendant inventory, bytes, modes and nanosecond mtimes. Extraction and subsequent relocated verification/build/provenance checks passed.
5. Thirteen additional probes passed: ZIP symlink, directory and FIFO types; mode mismatch; foreign platform; payload tampering; duplicate member; wrong manifest pin; duplicate JSON key; and missing isolation, enabled site, enabled bytecode or optimization flags. Every hostile-archive probe failed before creating its output directory. The duplicate-member fixture intentionally produces Python's duplicate-name warning when constructed.
6. Nested provenance authenticated the main and predecessor packets, fresh and inherited audits, sealed source ZIP, all retained dependency origins and nested Report26 release/source/scientific manifests and checksums. The main manifest remains `72f8024c49a364bfd26ccc9f0e89d128e4390c1bf045477aa3d584bba3eaea31`; the fresh audit manifest remains `befa9a29fd2c31a93bfecdda67794a830e5ebbedc71c4c76b85fd3fb4f161614`.
7. The reviewed 256-file source release and all four original source trees were identical at this review's before/after endpoints. Report70 itself was read and authenticated, never modified or executed.

## Historical qualification and limits

The historical short-exactness interval did **not** observe a static live Report70 tree: 49 file/directory entries were added and the existing `qa` directory's mtime changed from 1791127290722307959 to 1791127703586072608, with its mode unchanged. This was independently recomputed from inert evidence. The historical frozen inputs matched. The later independent audit's equal frozen/live endpoints do not erase the earlier qualification.

Endpoint comparison is not an atomic snapshot or proof of continuous immutability. Access times are outside preservation scope. Dependency locking covers executable/interpreter bytes and the recorded TeX/font inputs plus selected maps, not shared libraries, Python's standard library or the operating system. This review exercises authenticated release operations and named hostile cases; it does not certify resistance to arbitrary active filesystem races or resource-exhaustion attacks. It is not a scientific replay or a new mathematical audit.

The test-clone manifest (`1c0eff04a0f4dacce9bdb3dbf4be989b88d7d329a4e27547fb9af4719e1c7990`) and deterministic test ZIP (`05f886e66a64b88648866c34c895dddc08c97ef78f2bfabbd0280f8eb5c57191`) are review artifacts, **not** the owner's eventual final release seal.

## Evidence

`receipts/REVIEW_RESULT.json`, `COMMANDS.json`, both independent build receipts/locks/recorder unions, `SELFTEST_RECEIPT.json`, `EXTRA_ADVERSARIAL_RECEIPT.json`, `SUPPLEMENTAL_INDEPENDENT_CHECKS.json`, adaptation authentication, provenance receipts, complete endpoint snapshots and command stdout are retained. `review71.py` and `supplement71.py` preserve the reviewer-authored procedure; `INSPECTED_TOOLS.sha256` pins the fully inspected release tools. The compact dossier's `REVIEW_SEAL.json` authenticates its payload bytes and excludes itself and its digest sidecar; it is a hash identity seal, not a signature.

# Restore and check the 95-row supplement's pinned coefficient package

The tracked 95-row circuit names `../coefficients/BINDING.json`, but at
the start of this work that path, its four compressed payloads, and thirteen
other files required by the supplement's own frozen manifest were absent.
The [supplement manifest](../../../con-zfc-diophantine-forms/115-synchronized-exponents/supplement/MANIFEST.json)
has SHA-256 `b6f7ecd9dc2a6317dce88e01985a1d167e4aef77c393ff8a53c363eece72956d`.
It pins the missing binding and payload files. Each of the 18 absent files
was found at the retained parent or explicitly pinned upstream source path,
and each had **exactly** the manifest's SHA-256 before restoration. Their
total size is 122,953 bytes.

`restore.py verify` assembled an isolated supplement copy, filled only the
missing paths, and verified all 45 manifest entries. The supplement's own
`check.py` then passed in both normal and optimized Python modes and
reproduced the respective manifest-pinned `CHECK.json` files byte-for-byte.
An intentionally corrupted MF gzip payload was rejected. Before touching the
worktree, the script rechecked its inputs; `restore.py restore` then created
the 18 destinations exclusively, without overwriting existing files, and
rechecked every manifest entry. The original [verification receipt](observations/verify.json),
[restoration receipt](observations/restore.json), checker output
and corruption traceback are retained. `restore.py` SHA-256:
`397deb7d0c6c3820ef8d2c141bf3ca31f271445558e2147bea407496c53f3a9d`.
The restore mode is intentionally one-shot and refuses already existing
destinations; use `audit.py` with a fresh output directory for a repeatable
read-only recheck of supplement and parent inputs.

The restored circuit binding now resolves to bytes identical to the parent
`BINDING.json` (SHA-256 `dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01`).
The 95-row child has SHA-256
`2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`
and explicitly pins the 96-row parent SHA-256
`2a8da9ac141de5078fbdca96acccab5a7c44f6b39f4bc6063261b29179cb68be`.
Both have the same ordered fixed leaves `beta, K0, MC, MF`; the binding maps
them to `beta, K, MC, MF_source`, with **MF already shifted**. All four
restored gzip files are byte-identical to the retained parent payloads and
match the manifest and binding's compressed/raw hashes, lengths, bit counts,
and unsigned minimal little-endian encoding.

The `python3 -I -B audit.py` observation verifies the full
restored manifest, all 18 parent/source copies and binding target, and runs
the original supplement check in a fresh temporary copy in both Python
modes. It also reruns the pinned external beta, K, MF and 95-row graph
comparators; for MC it independently parses the pinned small Lean byte
recipe and compares all 73,759 bytes to the decompressed parent payload.
All checks exited 0, and supplement and source bytes were unchanged at the
recorded postchecks. Exact outputs and the successful machine-readable result
are in [`audit-observations-attempt05`](audit-observations-attempt05/), with
the actual bounded command and exit receipt in
[`observations/audit-attempt05`](observations/audit-attempt05/).
To repeat without overwriting evidence, run `python3 -I -B audit.py /tmp/supplement-audit-NEW`
with a fresh, nonexistent output directory.
The earlier successful audits, including the version before explicit
path-target and source postchecks, are retained as attempts 01–04. The fifth
also rechecks the MC Lean recipe source after running the external checks.
Attempt 01's `source.py` was reconstructed from the immediately subsequent
source by removing the two added postchecks, rather than captured at runtime;
the later attempts capture their own source at runtime.
`audit.py` SHA-256
`a78fb817cdb0f70870c60176f8f9197c6599a72d24452430be69f58288b5bd33`;
its result SHA-256 is
`b619f5591398d22b3016451083c9520f7c32b849c15baf1f769a4fb100c6a109`.
`run_audit.py` SHA-256 is
`4b397fa3272e7a131511f86a74d1ee4919d33f026767cc0aae7258cdcff7168f`,
and its exit-0 terminal receipt SHA-256 is
`5de910b9bcc3106be4b0b7e790c038cc1dca282eb65880f42475d7a430b50745`.

These are reproducible **external provenance and finite checks**. They do
not formalize SHA-256, the Python/Lean recipe transcriptions, gzip, the
filesystem, or the 95-row JSON parser in Lean. They do not prove that a PDF
displays this graph, a complete ancestry audit, or an iPRA derivation. The
existing Lean result concerns the separately defined closed byte recipes;
the relation of those sources to the restored files remains the recorded
external transcription boundary.

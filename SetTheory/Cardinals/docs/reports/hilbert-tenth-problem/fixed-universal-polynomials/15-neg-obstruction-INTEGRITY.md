# Integrity and reproducibility contract

## Trust anchor and complete identity gate

Before executing any packaged program, obtain the ZIP digest independently
and compare it with a digest computed by a trusted external hashing tool.
Alternatively, a trusted external implementation must authenticate the enclosing
MANIFEST.json and independently verify all its payload hashes, including the
normalized verifier hash. The manifest digest alone is insufficient: a substituted
verifier could falsely report success while retaining the authentic manifest.

After this bootstrap, the verifier pins the manifest, which inventories every
payload: article, PDF, tools, plans,
receipts, public review records and the complete frozen evidence. Only the one
manifest-pin line of verify_release.py is normalized to 64 zero digits when
hashing that file. SHA256SUMS also records its exact unnormalized bytes. This
breaks the circular hash dependency while detecting changed verifier code.
A release checked only by its own unauthenticated verifier is outside this
contract. Authenticating the complete ZIP externally establishes the executable
bytes before they run. Never reseal a received package to make it pass.

The complete source MANIFEST.sha256 digest is:
793b955c11fa905df10e69e93e0c02a3c64af8a6566c71b059fad8363e450e0c

The frozen EXACT-OBSTRUCTION.md proof digest is:
918b82b7666b4f5cbab5fd7a0b8298275ac62fe84f83261ef88ea863765d455f

The source checksum manifest lists exactly 25 unique payloads. Together with
that manifest, exactly 26 files are included under evidence/. Every original
byte is preserved, including any archival provenance text. The source-lineage
record maps all copied files and requires identical original and packaged hashes.
No source packet, earlier report or upstream file is modified by this release.

## Execution boundary

Only three mathematical programs are eligible for replay:
check_exact_obstruction.py, independent/audit_exact_obstruction.py, and
independent/audit_log_windows.py, all under evidence/. Their own SHA256 pins are
also fixed in the verifier. The complete evidence/sources/ subtree is inert data:
its Python program is neither imported nor executed, and its arithmetic
schedules are only inspected as literal static lists by the authored checks.

Before mathematical execution the verifier checks the enclosing manifest,
exact file and directory inventories, byte lengths, modes, hashes, source pins,
complete lineage, expected receipts and exact replay allowlist. It rejects
unexpected files/directories, missing paths, symlinks, special files, unsafe
names and checksum changes. It parses all JSON strictly. All release tools and
all three mathematical programs are statically checked for absence of assert;
upstream inert Python is exempt and is preserved unmodified. Final-stage
identity additionally requires both article files and an approved public release
review tied to the exact source/proof pins and the reviewed TeX/PDF byte hashes.

## Exact JSON and adversarial tests

Receipt comparison recurses through exact object key sets, list lengths,
values, and JSON scalar types. True is not 1, false is not 0, and 1.0 is not 1.
Missing/extra keys, wrong nesting, duplicate object keys, malformed syntax,
NaN, Infinity and overflowing floating literals are rejected. The explicit
checks remain active under -O. Self-tests reject 18 typed/structural mutations
and 12 malformed/nonfinite encodings, including nested cases.

The tamper test changes every release executable, every authored mathematical
program, inert upstream code/data, proof, manifests, plans, receipts, counts,
file/directory modes and path inventory in disposable copies. Both normal and
optimized verifiers must reject each changed tree at the identity gate, before
mathematical payload execution. These tests demonstrate rejection behavior;
they do not make a substituted verifier trustworthy without an external anchor.

## Fresh replay and preservation

A replay uses two fresh external copies, one for ordinary execution and one for
optimized execution. Each authored program writes a newly generated receipt to
captured stdout and independently checks its frozen expected receipt. The release
verifier then requires byte identity and exact recursive JSON equality. It
rechecks identity after each program and verifies that both the original and
copied release bytes, modes and modification times remain unchanged. No output
receipt is written into a source tree, and no bytecode cache is created.

The selected-grid checks corroborate exact arithmetic and finite exclusions;
they do not prove positivity at every scale, produce a full negative compiler
zero, or establish any claim of global novelty. The auxiliary tuple checks are
explicitly subsystem-only. Mathematical sufficiency is supplied by the proof,
not by a finite enumeration. This preservation mechanism is not an operating
system sandbox against malicious code: authenticate the archive independently.

## PDF and archive

The PDF builder copies the article source into a fresh external directory. It
uses three installed-local pdfLaTeX passes, no shell escape, UTC, a fixed source
epoch and suppressed PDF date/trailer identifiers. All format/font caches and
build logs are external. --check-packaged requires sealed identity first and
fails on any PDF byte difference. Reproducibility assumes the same TeX engine,
packages and fonts. The original tree must retain all bytes, modes and mtimes.

ZIP creation uses sorted regular-file entries, fixed date, modes and compression
settings. Checking requires an independent archive digest and a verified local
tree. It rejects duplicates, traversal, absolute/backslash names, wrong roots,
unexpected/missing/directory/symlink members, unsupported compression, encryption,
wrong sizes/modes and changed bytes before extraction. Only already matched
bytes are manually written into a new moved directory. Ordinary and optimized
identity checks must agree; optional replay runs the full three-program replay
under both verifier modes. Archive regression exercises hostile inventories in ordinary and optimized Python.

## Maintainer procedure

Engineering-preview sealing is solely for disposable QA copies. The public tree
must not be finally sealed or archived while mathematical approval is pending.
Final sealing requires the completed article/PDF and an approved release review.
The initial PDF can be built without --check-packaged before sealing. After
sealing, rerun identity, ordinary and optimized replay, tamper tests, two external
PDF rebuilds with byte comparison, deterministic archive creation, safe moved
extraction replay and archive regressions. Keep all generated logs and private
QA outside the release. Public records should summarize checked outcomes without
private paths. An edited payload requires a new seal and all affected checks,
followed by new independently communicated digests. Previous reports remain
unchanged.

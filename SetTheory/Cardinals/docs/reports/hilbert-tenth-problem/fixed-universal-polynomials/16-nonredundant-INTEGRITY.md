# Integrity, provenance and reproducibility contract

## External authentication is mandatory

Obtain the complete ZIP SHA256 independently and compare it with a digest from
a trusted external hashing tool BEFORE executing any packaged helper or checker.
Alternatively, externally authenticate MANIFEST.json and independently verify
all its payload hashes, including the normalized verifier hash. Authenticating
only the manifest is insufficient: a substituted verifier could retain the
manifest and falsely report PASS. Never reseal a received release to make it pass.

The enclosing manifest inventories article/PDF, helpers, plans, receipt tables,
review records and frozen evidence. Only the single MANIFEST_SHA256 assignment
in verify_release.py is normalized to 64 zero digits for that file's manifest
hash. SHA256SUMS additionally records its actual unnormalized bytes. This avoids
a circular pin while preserving executable identity. A release's own PASS is
not an independent trust anchor, and source authenticity is not mathematical truth.

The frozen source MANIFEST.sha256 SHA256 is:
b769c58935f5951b1ad4b23df0daa5a9c31e2a04ea734d7bb9916249e51e9c38

The frozen ALL-BUT-MAIN-PROJECTION.md SHA256 is:
d67a98bd95a1a11a8b1dc24c508c601f92c6758f9c4d92d9d4d13acb85936575

The frozen Jacobi MANIFEST.sha256 SHA256 is:
27203cb0baa757bbbf05d166c379dd9da8ceeeed084ec131cc9558749dae5cf4

The frozen JACOBI-ADDENDUM.md SHA256 is:
16311c258666483ed3342e3129966018e33a17ff0ec71aceca50540b1a75c98a

There are exactly 21 unique family payloads plus its checksum manifest, all
included under evidence/. Every byte is preserved. The exact lineage table maps
the 22 original and packaged identities. Packaged copies have release-normalized
permissions; the original frozen source and Report37 keep their bytes, modes and
mtimes. No upstream repository is changed and no upload is part of this release.

The complete Jacobi packet has 31 payloads plus its manifest. Its 22 inherited-
family members are identical to evidence/ and are stored only once. Ten new
members are copied byte-exactly under jacobi/. verification/jacobi-lineage.json
maps all 32 original addendum paths to exact packaged hashes. The enclosing
identity gate checks both frozen manifests before any of the three mathematical
programs executes. No frozen original is edited or normalized.

## Provenance and conditional mathematical scope

The theorem and reconstruction inherit the genuine-compiler/bootstrap premises
of the sealed Report37 theorem, whose complete TeX is included as inert context.
This release does not independently prove the universal compiler theorem.
The parity-source snapshots are pinned, inert evidence. The prior independent
review expressly records that complete77's remote provenance was supplied by
the author; its attempted independent network retrieval failed. Neither the
packaged hash checks nor this release claim a second network authentication.

The historical five-source authentication and unchanged 43-file sealed-tree
check in independent/historical_audit_receipt.json are preserved historical
claims, not checks re-executed by this portable replay. Portable replay checks
four packet-relative context snapshots and the exact local source packet.
The Jacobi context's ROOT-CHECK.json is also historical corroboration: its 42-case
root receipt is authenticated as bytes, not treated as a separately rerun checker.
The new Jacobi checker performs its own explicit finite tests.

The analytic proof, using quantitative derivative and discrepancy estimates,
establishes infinitely many solutions of the predicate with one congruence
omitted, conditional on the inherited premises. The Jacobi extension proves
(X/H)=(w/(4q^3+3)) for even square q with 3 not dividing q, including composite
and noncoprime cases. An odd-p hit requires symbol -1. The fixed thinning
r=(4q^3+3)j has symbol +1 and therefore gives certified misses. Reapplying the
shrinking-target proof to the thinned phase establishes infinitely many genuine
reduced candidates, with the dyadic count now in j, not the original r or w.

The raw residual is rho^2>0 and the positive21 residual is
[rho(2D-rho)]^2>0 on that thinned family. This proves nonredundancy of the raw
main projection comparison and, separately, the positive21 main norm comparison
relative to their respective remaining conjunctions. The unchanged earlier
packet's unresolved-miss status is historical. The addendum does not establish
a main-congruence hit, full negative zero or global sign theorem; symbol -1
is necessary only, and that sector remains unresolved. No feasible threshold,
exhaustive parametrization or global novelty is claimed. These are proof-level
conclusions; no giant genuine candidate was numerically materialized, and finite
fixtures do not prove analytic existence.

## Identity and execution boundary

The only mathematical replay programs are evidence/check_unwrapped_family.py,
evidence/independent/check_audit.py, and jacobi/check_jacobi_addendum.py, each with
a fixed SHA256 pin.
All context files are inert bytes. context/complete77.snapshot.py is not imported,
compiled, interpreted or executed; static source row/dependency checks treat the
saved schedule as data and do not evaluate it.

Before execution the verifier authenticates the full enclosing manifest, exact
files and directories, lengths, modes, hashes, source inventory, lineage,
strict expected receipt table and exact replay plan. It rejects extra/missing
paths, symlinks, special files, unsafe names and checksum mismatches. Final
identity requires an approved review tied to both exact source/proof identities and TeX/PDF
hashes. All executable helpers/checkers are statically checked for absence of
assert statements; the frozen inert context is exempt. Explicit exceptions
remain active under -O.

Python 3.9+ and exactly SymPy 1.14.0 are required for full replay. The SymPy
version is checked from installed distribution metadata before any mathematical
checker runs. The release never installs software. Installed Python, SymPy,
TeX/fonts, zlib and operating-system tools remain external trust dependencies;
the version label alone does not authenticate their code.

## Strict receipts and output safety

JSON parsing rejects duplicate keys (including nested keys), NaN, Infinity,
overflowing floating literals, malformed syntax and invalid encoding. Comparison
recurses through exact keys, lengths, values and scalar types: true differs from
1 and 1.0 differs from 1. Self-tests reject 18 type/structure mutations and 12
malformed/nonfinite encodings in both modes.

The family author and Jacobi receipts use their frozen expected files; the
independent receipt and its separate expected file are byte-identical. All three
are regenerated on stdout from authored arithmetic/symbolic code. The enclosing verifier checks
fresh stdout against frozen exact bytes AND typed JSON values. No receipt is
trusted merely because a stored file says PASS.

Fresh external copies are used for ordinary and optimized runs. Every source
byte, mode and mtime is checked before and after; bytecode generation is disabled.
This preservation check is not an OS sandbox against malicious code. External
archive authentication and trusted runtime dependencies are still necessary.

The Jacobi checker retains its original inherited-family/ path contract. Replay
first builds a separate external portable stage from authenticated jacobi/ and
evidence/ copies. Every staged file hash/mode, exact directory inventory and
executable pin is checked before it runs. The whole stage's bytes, modes and
mtimes must remain unchanged afterward. All 32 staged members correspond to the
frozen addendum manifest; this staging does not execute an inherited module.

Supported replay never calls any checker's --output option. Optional
--receipt-dir must name an absent external path with an existing parent; files
are created exclusively only after successful replay. Existing output paths and
paths resolving inside the release are rejected, including symlink aliases.
The frozen author checker itself permits overwriting an existing external output
and regards only evidence/ as its packet. The independent and Jacobi checkers require
new external files but also guard their packets rather than the enclosing release.
Their historical bytes are preserved, so their direct --output interfaces are
not the supported release output contract. PDF destinations must be new or empty
external directories; ZIP destinations must be absent external paths.

Tamper regressions mutate executable helpers, all three checkers, inert code/data,
proof, manifests, plans, receipts, scalar types, counts, modes and inventory in
disposable external copies. Ordinary and optimized verification must reject
before mathematical payload execution. Output regression checks protected and
existing destinations without changing the release or existing outputs.

## Deterministic PDF and ZIP

The PDF helper uses external copies, local three-pass pdfLaTeX, no shell escape,
UTC, fixed SOURCE_DATE_EPOCH and omitted PDF date/trailer identifiers. All caches,
format builds and logs stay outside the release. --check-packaged first verifies
sealed identity and then requires PDF byte equality. Determinism assumes the
same engine, installed packages and fonts.

ZIP creation sorts regular-file entries with fixed dates, modes and compression.
Byte determinism assumes the same Python/zlib. Checking validates the independent
archive digest and every archived name, count, size, mode and payload against
the authenticated local release BEFORE extracting or executing archive content.
Duplicates, traversal, absolute/backslash names, wrong roots, NUL names,
unexpected/missing/directory/symlink members, encryption, unsupported compression,
wrong size/mode and changed bytes are rejected. Already matched bytes alone are
manually written to a fresh moved extraction. Normal and optimized identity
must agree; optional replay runs both verifier modes. The hostile ZIP suite uses
disposable external archives and never blindly extracts any ZIP member.

## Maintainer procedure

Engineering-preview sealing is permitted only in disposable QA copies. Keep the
working release unsealed until the article/PDF and scientific review are ready.
Final sealing requires a completed, approved public release-review record tied
to exact TeX/PDF and both source/proof identities. That record is a transparent review claim,
not a cryptographic certificate or proof of mathematical truth.

After final sealing, verify both modes; replay; test typed JSON, tamper and output
guards; rebuild the PDF twice externally and compare bytes; create two ZIPs and
compare bytes; check moved extraction with full replay; run hostile ZIP tests.
Keep all generated QA logs outside the release. Any later payload edit requires
a new seal and affected rechecks, followed by new independently communicated
digests. Previous reports and source packets remain unchanged.

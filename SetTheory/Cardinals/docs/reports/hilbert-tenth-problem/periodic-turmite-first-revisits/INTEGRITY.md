# Report38 integrity and reproducibility contract

## Bootstrap trust

Authenticate the complete ZIP against an independently obtained SHA256 with a
trusted external hashing tool before executing any packaged helper. Alternatively,
a trusted external implementation must authenticate MANIFEST.json and verify
all payload hashes, including the normalized verifier hash. A manifest digest
alone does not establish that a substituted verifier is trustworthy. A release
checked only by its own unauthenticated code is outside this contract. Never
reseal a received package to make it pass.

The enclosing verifier pins MANIFEST.json. The manifest inventories every
payload, including all release tools, article/PDF, review and replay records,
and the complete frozen source packet. Only the single MANIFEST_SHA256 line in
verify_release.py is normalized to 64 zero digits when hashing that file.
SHA256SUMS separately records its exact, unnormalized bytes. This breaks the
circular pin dependency without exempting any executable code from hashing.

## Frozen source identity

The source packet is retained under evidence/source-packet/ with every original
byte unchanged, including all original logs, its original verification script,
and the complete boundary-context subtree. The source manifest digest is:

7dfd4f270ad7bf667bc123aace7bd97fd13b992949a9dfc8e3dca3f8105cea62

The frozen PROOF.md digest is:

d4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12

The pinned source manifest lists 30 payloads; with that manifest there are
exactly 31 files. verification/source-lineage.json maps every copied file to
its original relative path and identical original/packaged SHA256. Source
history, original timings and original receipt provenance are not rewritten.

## Identity and execution boundary

The enclosing verifier checks exact files and directories, regular-file types,
path safety, lengths, modes, hashes, strict JSON, source pins, lineage, replay
plan and expected receipts before scientific execution. Unexpected directories
are rejected as well as extra/missing files, symlinks and special files. Every
enclosing Python tool is manifested and checked for absence of removable assert
statements. All six active source files are separately hash-pinned and checked
for absence of removable assert statements. Final-stage identity additionally
requires an approved release-review record identifying the exact TeX/PDF bytes,
source/proof pins and passing original-source replay.

The six active files are one_visit.py, observations.py,
test_boundary_regression.py, test_observations.py, independent_checks.py and
example.py. For each of normal and optimized Python, the verifier creates a
fresh external release copy and a separate runtime containing only these six
files. Python runs with -I and -B; the current directory, PYTHONPATH and user
packages do not enter the import path. The isolated runtime is explicitly added
for the pinned active libraries. The only entries executed are the 16 author
tests via unittest, the seven independent tests, and example.py. Their exit
codes are checked explicitly; no assertion-based gate disappears under -O.

The archived source verify_release.py is never invoked. Its dynamically measured
hash baseline is not used as an authenticity gate. No boundary-context program
is imported, executed, or staged in the active runtime. The active
test_boundary_regression.py is explicitly approved despite sharing original
bytes with the archived boundary test. These controls are an authenticated
execution allowlist, not an operating-system sandbox against malicious code.
The standard Python interpreter/library and installed TeX toolchain are trusted
external dependencies rather than bundled, pinned executables.

## Outputs, stable comparison and preservation

Original and copied release bytes, modes and mtimes are checked before/after
execution. The six-file runtime is checked after each command. Bytecode caches
are disabled. Output paths inside the release, including paths resolving there
through a symlink and hostile TMPDIR settings, are rejected before creation or
temporary-directory probes. All replay/build/archive QA must remain external.

Author and independent stdout and stderr are combined in the same order as the
frozen .log files. The only normalized text is the elapsed-time value in exactly
one unittest summary line with the expected test count. The entire remaining
output, including test names, success/failure suffix and printed scientific
counts, must match the frozen receipt. Both modes must agree after this narrow
normalization. Example output must equal the frozen JSON bytes and recursively
match exact JSON types, keys, lengths and values. No other scientific field or
formatting is discarded.

The strict comparator rejects booleans substituted for integers, integers for
floats, extra/missing keys, list-length differences and other type/structure
changes. The parser rejects duplicate JSON keys, malformed JSON, NaN, Infinity
and overflowing floating literals. Built-in tests cover 18 typed/structural
mutations and 12 malformed/nonfinite encodings in both Python modes.

Tamper regression changes release helpers, all active source files, inert
source code/data, proof, manifests, receipts, plans, original logs, inventory,
file/directory modes and checksums in disposable copies. Both verifier modes
must reject each mutation at the identity gate, before scientific execution.
Separate path-boundary probes demonstrate rejection without release mutation.
These tests validate rejection behavior, not authenticity without external trust.

## PDF and archive

build_pdf.py copies the self-contained article source to an empty external
directory. Three local pdfLaTeX passes run without shell escape, with UTC and
SOURCE_DATE_EPOCH=1790985600, omitted PDF dates and empty trailer identifiers.
Format/font caches and logs stay external. --check-packaged first requires
sealed identity and then exact PDF byte equality. Reproducibility assumes the
same installed TeX engine, packages and fonts; the helper does not download or
install them. All original release bytes, modes and mtimes must be unchanged.

archive_release.py creates sorted regular-file entries with fixed timestamps,
modes and compression. The final stage is required. ZIP checking requires an
independent archive digest and a verified local tree. Member count, safe names,
root, regular-file mode, size and every byte are checked before extraction.
Duplicates, traversal, absolute/backslash names, symlinks, directories,
encryption, unsupported compression and unexpected/missing/changed members are
rejected. Only matched bytes are manually written into a new moved directory.
Both verifier modes must agree; --replay repeats the full scientific replay
under both outer verifier modes. Hostile-archive regression tests both modes.

## Maintainer procedure

Only seal engineering-preview copies for disposable QA. Final sealing requires
the complete article/PDF and exact-byte approval; the report owner must approve
it after original-source replay. The first article can be built before sealing.
After final sealing, run normal/optimized identity and replay, tamper regression,
two external PDF builds with --check-packaged, two deterministic ZIP creations,
safe moved ZIP replay and hostile-archive regression. Store generated receipts
outside the release; include only curated public review records before sealing.
An edit to any release payload requires a new seal, affected rechecks and newly
communicated independent digests. Earlier reports and frozen source packets
must remain unchanged.

Finite checks corroborate the report's arithmetic and observation queries.
They do not replace the proof, extend its one-visit boundary, or establish
claims of novelty or broader computational universality.

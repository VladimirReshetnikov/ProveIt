# Integrity and reproducibility contract

## Authentication boundary

The independently delivered archive or enclosing MANIFEST.json digest is the
trust anchor. The verifier carries a fixed enclosing-manifest SHA256. The
manifest pins every delivered payload, including the verifier, other tools,
proofs, plans, copied receipts, and expected receipts. Only the verifier's own
single manifest-pin line is normalized to 64 zero digits when hashing that one
file. SHA256SUMS additionally records the exact, unnormalized verifier bytes.
This avoids a circular digest while detecting changed verifier code. An attacker
who replaces both the program and all externally supplied trust anchors is
outside this contract. Do not run seal_release.py to make a received package pass.

The source MANIFEST.json digest is
99e4371291d46d7ee8ef4821254ad702791e9b84060e69336d652e603c059ee1.
The unchanged approved predecessor compiler digest is
bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2.

## Exact source inventory

The source manifest has 16 payload rows. Together with the source MANIFEST.json
and SHA256SUMS, exactly 18 files are included under evidence/real/. The source
manifest is authoritative: unlisted bytecode caches are not copied. Every copied
byte is unchanged, including the approved_base compiler/proof pair. That pair is
selected predecessor context, not a copy of the complete previous report packet.
The source-lineage record maps all 18 files and records identical original and
packaged hashes. The frozen source checksum list is verified independently of
the enclosing release inventory.

## Identity before execution

verify_release.py imports only standard-library modules. Before any authored
payload import or execution it checks its pinned manifest, exact regular-file
and directory inventory, names, hashes, byte lengths, modes, source pins,
complete lineage, strict receipt values, replay plan, JSON syntax, and absence
of optimization-disabled assert statements. Unexpected files, directories,
symlinks, special files, mode changes, missing paths, unsafe names, and checksum
changes are rejected. The complete frozen main/optimized receipt pairs must
also be byte-identical. A final package additionally requires the article and a
release approval record tied to the exact source manifest and base compiler.

## Strict recursive JSON

Object key sets, list lengths, scalar values, and exact Python JSON types must
match at every level. In particular true is not 1, false is not 0, and 1.0 is not
1. Extra keys, missing keys, wrong nesting, duplicate object keys, malformed
syntax, NaN, Infinity, and overflowing floating literals are rejected. No check
relies on Python assert, so it remains active with optimization enabled. The
self-test covers nested boolean/integer and integer/float substitutions,
structural mutations, duplicate nested keys, and nonfinite values.

## Replay and source preservation

Full replay requires installed SymPy 1.14.0. The main exact checker regenerates
18 expansion/ledger cases and nine real-support branch instances (1,863 branch
attempts). The independent checker regenerates 54 coefficient/ledger cases and
uses its own sparse expansion of compiler-provided affine forms, without the
main expansion checker or Summand.records. It does no LP search.

There are two fresh external replay copies, one ordinary and one optimized.
Each producer's expected output is removed only in its external copy and must be
newly created. Its exact bytes and recursively typed values must match the
frozen reference, and stdout and receipt hashes must agree between modes.
The identity gate is re-established after each producer. The original tree is
snapshotted and must retain all bytes, modes, and modification times. This is
filesystem preservation, not an operating-system sandbox against malicious
code; execute only after validating the independent trust anchor.

The finite branch search is solver-assisted regression evidence. It performs
exact equality elimination and checks every returned point against all original
conditions. Rejected branches have no independently checked Farkas certificates.
The general all-real theorem is established by the mathematical proof, not by
finite testing or by solver rejection counts.

## Build and archive

The PDF builder copies only article source to an external empty directory. It
uses an installed local pdfLaTeX, three passes, explicit no-shell-escape, UTC,
a fixed source epoch, and suppressed PDF date/trailer identifiers. Font-format
cache work is external. It reports whether rebuilt PDF bytes match the packaged
PDF and checks original bytes/modes/mtimes. Byte reproducibility assumes the same
installed TeX environment, fonts, and packages.

ZIP creation is deterministic for a fixed finalized tree. It uses sorted
regular-file entries, fixed timestamp, modes, and compression settings. Checking
requires an independent archive digest and authenticates the local tree before
examining the archive. It rejects duplicate, traversal, absolute, backslash,
wrong-root, unexpected, missing, directory, symlink, encrypted, size/mode-changed,
and byte-changed members before extraction. Only already matched bytes are
written into a fresh moved directory, then checked with and without -O. Optional
full replay reruns all copied producers from that moved extraction in both
verifier modes. The original release must remain unchanged.

## Release procedure

Engineering preview sealing is solely for disposable QA copies. Final sealing
requires the approved release review and completed article. Final or archive output
must not be produced while approval is pending. After final sealing, keep all
new replay, build, archive, and regression output outside the release. If any
payload is edited, repeat sealing and all affected tests, then deliver new
independent digests. Never replace or edit the previously delivered Report35 or
the frozen source packet as part of this release.

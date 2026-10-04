# Independent review of the uniform-sector presentation release

## Verdict and exact boundary

PASS for the presentation-only tools, preservation boundary, and stable v2
article replay described below. No blocking defect was found in this scoped
workflow. This is an independent tool/release review, not a new mathematical
check, scientific rerun, or a final root-release seal.

The reviewed source is `/workspace/shared/oeis-uniform-sectors-release-20261004`.
A metadata-preserving external review snapshot was captured at approximately
2026-10-04 16:33:33 UTC, with equality of source-before, source-after, and copy
inventories over 340 files and 35 directories. The stable article, tools,
input pins, and dependency lock are pinned in `REVIEW_RECEIPT.json` and
`evidence/INDEPENDENT_REPLAY_RECEIPT.json`. Final README identity text and
independent review QA were still being assembled after this snapshot. Those
later administrative additions are intentionally outside this candidate's
manifest and ZIP. Root must authenticate the completed inventory, perform
final sealing and a separate post-seal terminal gate, and own delivery.

The accepted v2 article PDF is SHA-256
`e1689dc2ba86b8a1c01ac33897007bcafa3e6454f197b87920e56af87235b1df`.
Both self-contained TeX copies are SHA-256
`d0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191`.
The manuscript pin-map is
`10ddbdee2fc822c63b437b3e4b84c57717d3ed7934f63aa05952f0e1aac19164`.
The dependency lock is
`6ee7f579ad072c7c57d76341d35c51742f8b976c40816ad305b12a9836f35d07`.

## Inert inspection and execution scope

Before executing a release tool, I read every line of `freeze_inputs.py`,
`release.py`, `build_article.py`, `selftest.py`, and `tools/README.md` as inert
text. Their exact reviewed bytes are retained in `reviewed-tools/`. I also read
the complete v1 article as inert TeX, the exact caption-only v2 difference,
the dependency lock, and the preservation/replay documentation. The pinned
manuscript is self-contained presentation TeX. Scientific contents under all
`inputs/` trees, supplied scientific checkers, source/algebra interpreters,
physical or trajectory simulators, schedules, Lean, and the predecessor's
presentation tools were never run or imported.

The only release code executed was the reviewed current top-level owned
presentation tooling, including its byte-identical copies in fresh external
fixtures and the review candidate. I independently authored three small
presentation-audit scripts and a compact-dossier assembler, inspected each
completely before execution, and retained them under `reviewer-tools/`. They perform hashes, metadata comparison,
ZIP parsing, raw recorder parsing, and synthetic rejection tests. Imports from
release source were restricted to the reviewed current `release.py` and
`build_article.py`. Synthetic TeX tests do not constitute scientific evidence.

## Preservation findings

Independent direct filesystem/byte inspection confirmed all of the following:

- The pinned proof `ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65`
  and audit `4fa84b2ddfe383668c86ea0ad4d7419b0304eb0d9a97725aecbdab7e3b63ff03`
  match their frozen copies
- All 14 source-packet files, 18 independent-audit files, and 176 predecessor
  release files match their original bytes, permission modes, and nanosecond
  mtimes. Their complete directory metadata also matches
- All five source-seal companions were copied with those same metadata fields
  preserved; the three archive payloads have exact file inventories, bytes,
  regular-file kinds, and expected member modes
- The frozen input inventory is exactly 213 files and 26 directories, excluding
  the inputs root; that root's metadata is separately pinned
- All 355 scoped original objects match the original pre-freeze inventory, with
  no unrecorded descendants beneath inventoried original directories
- Source historical before/after records retain their original 51-object
  boundary; audit records retain their separate 333-object boundary. Every
  current scoped object agrees with the historical record, and the former
  scope is contained in the latter
- The full predecessor release and its archive remain unchanged. The
  predecessor manifest is authenticated by
  `313fe6210e10e3053ff518a591dc46c86c29681618775be67f0f87474ca4584c`;
  its archive by
  `821a1cfc1c00fd6d109ee2f6ff8007b4e8985f03d45f6f9a04d07aa8623fde27`

Access time, ctime, ownership, inode allocation, and directory allocation size
are outside this claim. No original content or metadata was repaired. The
predecessor's qualifications about earlier Report69/70 changes remain intact;
this review makes no whole-historical-workspace preservation assertion and
cannot retroactively broaden earlier observation intervals.

The preparer's recorded first freeze refusal correctly concerned the
predecessor manifest's documented self-mode exception: the on-disk manifest
is 0444 while its ZIP self-entry is normalized to 0644. The final freeze tool
handles only that explicit exception. The recorded first locked-build refusal
was a QA-file addition during its interval; the final exact build was rerun
with writes paused. Neither event required changing a scientific input.

## Static tool findings

`freeze_inputs.py` authenticates independently pinned proof/audit manifests,
archive inventories and payloads, the predecessor manifest/archive, and both
historical preservation scopes. It uses only standard-library filesystem,
JSON, hashing and ZIP operations. Final `verify-originals` checks the existing
scope and original set completeness without repairing it.

`release.py` validates exact frozen-input bytes/modes/mtimes and object sets;
rejects nonregular, symlinked, hardlinked or aliased entries; refuses fresh
output paths that overlap the release or protected source trees; rejects JSON
duplicate keys and noncanonical archive paths; and binds the current input
map to a literal inspected hash. The extractor authenticates all member
payloads and metadata before creating its destination, then restores file and
directory modes and nanosecond mtimes. The manifest intentionally excludes its
own content/self-metadata and release-root metadata. These are documented
noncircular boundaries, not omitted protected payloads.

`build_article.py` hashes its owned helper against a literal pin before loading
it. It checks the externally supplied manuscript pin and exact dependency-lock
digest. A fresh format is built with `pdftex -ini`, in an explicit external
work directory. The environment is replaced rather than inherited: home,
TeX configuration, variable/cache directories, formats and selected lm/cm font
maps are isolated; shell escape and automatic font generation are disabled.
It performs exactly three TeX passes, copying each recorder before the next
can overwrite it, and includes the format recorder and selected maps in the
union. All locked system inputs and seven executable/interpreter entries are
hashed before execution; observed union equality and repeat hashes are checked
afterward. Bootstrap is separately labeled and cannot claim locked replay.
It verifies PNG CRCs, raster structure/decompression and page inventory, and
records preservation both on success and failure.

These are scoped reproducibility and integrity controls. The dependency lock
is not a full environment image: shared libraries, Python's standard library,
and the operating system are not inventoried. Static inspection of the pinned
manuscript remains essential; no claim is made that a small TeX input-pattern
check is a complete validator or security sandbox for arbitrary untrusted TeX.
Read-only modes and SHA-256 are not signatures, WORM media or trusted timestamps.
Mathematical and all-page visual review are separate model-performed gates.

## Independent execution findings

I reran the complete owned synthetic suite in a new external output directory:
39/39 PASS. I independently authored 19 further hostile probes: 19/19 PASS.
They cover changed/missing frozen bytes, changed input-pin maps, duplicate JSON
keys, changed helper digest, Python optimization, stale executable pins, an
extra preflight-valid but unexecuted system input, ZIP payload/mode/symlink/
duplicate-member attacks, wrong external archive pins, existing extraction
outputs, malformed PNG row filters, raster lengths and dimensions.

The added unused dependency is important: its bytes pass preflight, but the
post-execution exact-union gate refuses it. The owned first-pass-only fixture
likewise proves that a dependency loaded only on pass 1 is retained and cannot
be omitted from the lock. Hostile TMPDIR/TEMP/TMP runs preserved their fixtures.
Refusal outputs, full test receipts, reviewed harness source, and exact external
fixture inventories are retained, rather than relying on a preparer's PASS
claim. None of these tests modifies the actual release or originals.

Two independent exact v2 builds succeeded: one from the external review
candidate and one after authenticated ZIP extraction to a different directory.
Both PDFs match the accepted 12-page PDF byte-for-byte. The extracted PDF text
and all 12 PNG raster bytes also match each other. Each replay has a fresh
format, three compilation passes, exact dependency lock equality, no final
layout/reference warnings, and unchanged candidate tree during the run.

I separately parsed all four raw `.fls` recorders for both replays and every
selected font-map result. Their union is exactly the 190 system inputs in the
lock. All non-system inputs are the manuscript and generated local format,
map, auxiliary and outline files; there is no input from a scientific tree.
The lock has seven interpreter/executable entries. Raw recorders, pass logs,
preflight/union receipts, page inventories and preservation snapshots are
retained in compact form; duplicate PDFs/raster sets remain external.

The candidate ZIP was created twice and both complete byte strings agree:
`bacc81510a251f259ec97a7cf998d2fcfea40c81dce20e0b77a5388cd1fccb93`,
16,289,848 bytes. Its candidate manifest pin is
`1e30b1208e143ca62d608dad28411d32fa89d3cc9ebecbe8cdf2f7f56e2dbff6`.
ZIP ordering, timestamps, compression, modes, exact inventory, CRC and every
payload were independently checked. Extracted file and directory metadata
matches the authenticated candidate manifest exactly. These are review-
candidate pins, not the future final release's delivery pins.

## Retained review boundary and next gate

Only the complete `qa-copy/` directory is eligible for copying into the final
release, recommended destination `qa/independent-release-tool-review/`.
Its `REVIEW_MANIFEST.json` binds every other retained file and directory by
exact relative inventory, byte length, SHA-256, permission mode and nanosecond
mtime. It excludes its own metadata/content and the qa-copy root metadata.
The detached manifest hash is reported directly to the owner. All owned
compact dossier files are sealed read-only; their snapshots are inert evidence.

Large copied synthetic fixtures, candidate/extracted trees, duplicate archives,
PDFs and rasters remain in the external dossier without deleting prior tests.
`EXTERNAL_EVIDENCE_INVENTORY.json` identifies those exact external bytes and
metadata, including intentionally hostile symlink fixtures. The compact dossier
retains all full reports, receipts, reviewed tool sources, independent harnesses,
negative-probe outputs, compact logs, raw recorders, dependency/PDF/raster pins,
preservation inventories and candidate manifest. It does not redundantly copy
all fixture payloads or raster images into the deliverable.

The root final-seal coordinator must preserve this authenticated dossier
boundary and frozen inputs, then authenticate the completed release manifest,
repeat deterministic archive creation, perform metadata-restoring extraction,
and run the separately owned post-seal terminal gate before delivery. Any
change to the pinned article, tools, input map or dependency lock invalidates
this review's exact-artifact acceptance and needs renewed review.

## Final documentation correction and coordinator inspection

After the candidate snapshot, the root README changed “Human all-page inspection”
to “All-page visual inspection,” and tools/README changed its one occurrence of
“Human” to “Visual.” I inspected the exact tools/README diff; no executable tool,
article, frozen-input or dependency-lock byte changed. The final tools/README
is retained and pinned at
`f29b0697161437a3e1c3a39781d6e957e67312944a50d072ba7faa7a57496f9e`.
The candidate archive still authenticates the earlier documentation snapshot;
this final documentation-only correction is covered by the independent review
and final root inventory, not retroactively attributed to that archive.

I also read every line of the owner's external final-seal coordinator,
`oeis_uniform_finalize_release_20261004.py`, as inert source. Its SHA-256 is
`084a3ab0ff2ca4f80cf4f7589fadbc2e2c62bb31af7d1a734e6570c6b05e72c7`.
No unsafe orchestration was found. It checks reviewed tool/artifact/review pins
and final visual acceptances before changing modes; preserves the full inputs
and both independent-review subtrees; seals only owned content; generates
external manifests and deterministic archives; authenticates metadata-restoring
extraction; and delegates exact replay to the already reviewed owned tooling.
It checks the original boundary and preserved subtrees again afterward.
The coordinator was not executed by this reviewer. Its final artifact hashes
and fresh-output behavior mean a partial failure needs explicit diagnosis,
not blind rerun. Its actual execution and a separate post-seal terminal gate
remain the owner's responsibility. A byte-exact inert snapshot is retained in
`reviewer-tools/`.

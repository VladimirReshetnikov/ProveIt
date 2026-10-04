# Independent presentation-release tooling review

## Decision

**ACCEPT the inspected candidate's presentation and packaging tooling. No tooling
corrections are required.** This is a candidate review, not the later final
release-manifest gate. Mathematical and human full-page visual acceptance are
separate reviews; this review independently checks compilation, every raster's
integrity/equality, source freezing, safe packaging, and preservation.

The original candidate was observed unchanged from the stable copy at
2026-10-04 15:54:18 UTC through the closing inventory at 15:56:10 UTC. These
are local filesystem/clock observations, not trusted external time attestations.
The owner was then told that QA additions could resume.

## Authenticated identity

| Object | SHA-256 |
|---|---|
| Article TeX | `6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c` |
| Accepted and twice independently rebuilt PDF | `2a95d839ec43787f55cd73a7cb8e6a65635210388398f33b30396910cc128910` |
| Manuscript pin map | `f330e99fd48b98ce57b1b205416d98acda22dbff63ca6ab2c0a769919120250d` |
| Exact build-dependency lock | `01477b108b9576ce8fe0fc3ee516e1c106e684940d335a6fe694c675e5e60f79` |
| Frozen input pin map | `a831a8433e0c85cd108df9a5f559428069ba8cec8cf302d2569087c5b63ccadb` |
| Machine review receipt | `12210012567c7af27d83afee0a0109f0186f0a9c3ce2238d7e38847e5e65af82` |
| Independent recorder review | `c721af40fda7f75be3a2f89c73331c8ddbe772662b59814421254a4a6e5232c4` |

The four owned tool hashes are in `REVIEW_RECEIPT.json`. All four tools were read
in full before any execution: `release.py` (303 lines), `build_article.py` (243),
`freeze_inputs.py` (207), and `selftest.py` (183). The pinned article TeX was also
read before typesetting. Both reviewer-authored verification scripts were fully
read before execution.

## Established results

1. A fresh metadata-preserving candidate copy exactly matched the original
   inventory. File bytes, permission modes, nanosecond modification times, and
   directory modes/times matched. Access times and inode identities are not
   portable preservation claims. The original candidate remained unchanged during
   this review interval.
2. The frozen 46-file input map matched independently reconstructed inventories.
   Both complete upstream packets matched their originals and externally pinned
   source manifests, with exact payload file sets. All four selected closure
   dependency files matched their original bytes and metadata.
3. Independent JSON differencing reproduced the authentic 249-before/376-after
   historical inventories and exactly 132 differences, split 44 in Report69 and
   88 in Report70. The retained source/audit historical records were byte-equal.
   All 62 core entries were equal in both historic records and the live original
   paths. The separate 994-entry fresh scoped original inventory also matched at
   the start and end. This does **not** claim preservation of the active report
   trees over the historical interval.
4. The locked build uses Python isolation flags, a minimal environment, a fresh
   temporary work directory under the explicit output, a freshly initialized TeX
   format, three compilation passes, and `-no-shell-escape`. The article consumes
   the newly created local format in every compile. The source trees are never
   imported or executed. Font generation is disabled; selected font maps are
   recorded. The source inspection and retained recorder inputs are consistent
   with the declared presentation-only boundary.
5. The external lock was authenticated before execution. The resulting dependency
   receipt was byte-identical to that lock. I separately parsed the actual four
   retained `.fls` files, rehashed their external inputs, and reconciled their
   exact sets with the recorder receipts: 64 external inputs for format creation,
   202 for each compile, and 264 in the exact union including the selected maps.
   Seven interpreter/executable entries are locked. Shared libraries, Python's
   standard library, and the operating system remain outside this declared lock.
6. The independent locked PDF matched the accepted PDF exactly. Every one of its
   16 PNG pages was independently CRC-checked, decompressed, checked for its full
   raster length and filter values, and matched by dimensions, bytes and SHA-256
   against the accepted page inventory. The same PDF and all 16 raster identities
   were reproduced after metadata-preserving archive extraction and relocation.
7. All 39 owned synthetic release tests passed. They include a first-pass-only
   dependency retained in the all-pass union; omitted and stale lock refusals;
   hostile temporary-directory variables; pin, output, source mode/time, symlink,
   hardlink, extra-file and empty-directory refusals; corrupt PNG rejection;
   manifest tamper and collision rejection; deterministic ZIPs; extraction; and
   relocated synthetic PDF equality. These remain owned synthetic tests, not an
   independent scientific computation.
8. Two independent candidate archives were byte-identical. The owned extractor
   restored all manifest-covered file/directory modes and nanosecond mtimes, and
   all payload bytes. Independent comparison of the extracted inventory to the
   manifest passed before relocated verification and replay.
9. Five reviewer-authored malformed-archive probes were refused with exit status
   2 before creating extraction output: extra traversal member, duplicate member,
   symlink member, changed member mode, and corrupted payload bytes.

## Boundaries and interpretation

- No scientific program in the originals or `inputs/` was executed, imported,
  evaluated or modified. No source interpreter, physical or trajectory simulation,
  saved schedule, Lean, upload, publication or external communication was run.
- The first packaged build record legitimately has `packaged_pdf_match: false`
  because it predates copying that accepted PDF into the package. Both independent
  replays use `--require-packaged-match` and record `true`; no contradiction remains.
- The tooling authenticates exact trusted pins and detects observed mutations.
  This is not an operating-system security audit, a defense against a concurrent
  privileged adversary, an immutable-storage guarantee, or a universal untrusted
  TeX sandbox. The inspected pinned manuscript and explicit no-shell-escape build
  are the accepted execution scope.
- The non-self-referential release manifest intentionally excludes root-directory
  and manifest-self metadata. Its normal extractor restores manifest-covered
  metadata; generic ZIP extraction need not preserve nanosecond timestamps.
- The candidate snapshot manifest and ZIP recorded in `REVIEW_RECEIPT.json` are
  review artifacts. They are not the final release manifest/archive, which will
  include subsequently added acceptance QA and requires the separate final gate.

## Evidence

`sealed-evidence/` is the compact evidence packet. Its manifest covers every
contained file by bytes, mode, nanosecond mtime and SHA-256, plus directory metadata;
it excludes only its own manifest. The detached manifest pin is supplied outside
that folder. It contains this report, the independently authored scripts,
authenticated subject tool sources, observed candidate inventories, build and
recorder receipts, all four recorder files for each independent build, page
inventories, owned-test results and refusal/operation logs. Larger temporary
fixtures, PDFs, rendered pages, and candidate archives remain in the enclosing
review workspace but are not needed to transport the compact evidence packet.

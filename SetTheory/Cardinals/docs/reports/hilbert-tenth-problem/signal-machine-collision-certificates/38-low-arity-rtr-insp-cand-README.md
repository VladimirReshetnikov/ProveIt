# Report 69

## Low-arity finite-clipping Diophantine compilers

4 October 2026. Read `Report69.pdf` for the complete article. `Report69.tex` is the matching flattened editable LaTeX; seven readable modules are retained in `manuscript/`.

The native two-witness compiler represents every fixed finite clipping table on positive integer pairs with a unique positive witness pair, five residual squares and exact degree max(2K,4,2 deg F_S), at most 4T for K=T+1 and T>=1. Horizon zero has its own degree-two formula. One fixed two-zero-test program attains degree 4T for every by-horizon T>=2 in this presentation; the exact-time distinction is explicit.

The separate one-witness polynomial is a product of disjoint-cell sums of squares. It has one unique positive native witness and exact degree 2 n_I+4T n_E+8T n_C. Its collected support and expanded storage ceilings are paid separately from its compact O(K^2)-gate circuit and potentially exponential distributed SOS length. A full coefficient, support, storage, arithmetic-operation and finite-table-preprocessing ledger is included for both constructions.

The article proves the exact zero-versus-one native auxiliary-variable classification for a fixed finite clipping table with no degree restriction. Zero variables suffice exactly when every accepted tail cell has its full coordinate-flat closure in the accepted table. The same classification and a one-witness construction hold in each fixed finite input dimension. This is a scoped finite-table theorem, not a global MRDP minimality result.

Paid composition with the accepted twelve-leaf POWER module gives 28 positive witnesses, 31 total variables and 17 square slots. The one-witness alternative gives 27 witnesses and 30 total variables: 12 squares plus a nonnegative product block, or exactly 13 squares after squaring that block and doubling its native degree contribution. All full composed fibers are infinite despite unique decoded/native projections. No unbounded-horizon fixed polynomial, global minimum arity, minimum degree, novelty, priority or new physical-dynamics claim is made. Reports 66–68 and their original valid bounds remain unchanged; Report67's accepted parity refinement is included for comparison.

## Included source and independent mathematical acceptance

- `science/low-arity/`: the complete unchanged frozen source packet, its proofs, source evidence, historical preservation record and dependencies
- `audits/low-arity-independent/`: the complete accepted independent audit with its fresh exact-algebra evidence and successful relocated replay record
- `science/exact-degree-comparison/` and `audits/exact-degree-comparison/`: complete unchanged Report67 comparison source/audit; their scientific programs and saved evidence remain inert
- `INPUT_PINS.json`: exact original locations and copied file/directory metadata for 85 files and 12 directories, plus both scope-root records
- `qa/`: presentation provenance, source checks, owned synthetic tests, build/render receipts, page images, owner visual review and independent presentation reviews
- `tools/`: Report69-owned presentation build, release and synthetic selftest programs
- `RELEASE_MANIFEST.json`: final release inventory, authenticated by a digest obtained outside the archive

The low-arity source manifest SHA-256 is:

`b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82`

The complete low-arity audit verdict is PASS with no mathematical correction. Its audit text SHA-256 is:

`6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe`

Its manifest SHA-256 is:

`6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3`

That audit covers both native compilers, all stated costs, the closure classification, the fixed-dimensional extension and both paid compositions. The earlier two-witness-only review remains included with its narrower scope intact. The exact-degree comparison audit accepts the parity law with the local odd-K symmetry argument explicitly restricted to K>=3; horizon zero is separate.

The full independent audit records 48 two-witness and 28 one-witness expansions, all 530 two-dimensional tables through K=3, additional dimension tables, instrumented circuit ledgers, full POWER/gap expansions, 14 complete source coefficient comparisons, and a successfully relocated algebra replay. One large squared-block case is certified by its exact degree and the proof of degree doubling, not misrepresented as a completed self-convolution. Those are the independent audit's stored results, not newly executed report checks. All-input correctness comes from the proofs and the explicitly imported constructive Pell theorem pair.

The source's historical preservation record retains a genuine 17-entry change list during concurrent Report68 pre-seal work. Its initial whole-interval preservation assertion was interrupted, and its original baseline and log remain intact. A separate later inventory verified the final Report68 manifest and its 332-entry post-seal interval. This report does not claim that the earlier interval was static. The fresh Report69 baseline separately checks current original inputs and copied metadata without modifying them.

No scientific program in `science/` or `audits/` is imported or executed by Report69 tools. There is no author/upstream scientific execution, counter interpreter, physical simulator, saved schedule or Lean build. The accepted Report68 presentation README and all three tools were read completely before the fresh Report69 adaptation; copies remain inert in `qa/predecessor-tools/`. Authoring-only preparation scripts in `qa/` are historical records with local paths, not portable replay commands.

## Presentation acceptance

The owner inspected all final page images and corrected the initial overfull source-path line and two small layout issues before the final render. The exact locked packaged-PDF replay and all 39 owned synthetic tests passed. The independent mathematical-transcription/page review and release-tool review are in progress at this candidate stage; their accepted final dossiers will replace this status before sealing. A fresh root terminal verification is performed separately after the final archive is sealed, so its later receipt is not claimed to be inside that archive.

The primary literature context is narrow: NIST DLMF 3.3(i) for ordinary Lagrange interpolation, and the author-hosted primary text of Noga Alon's 1999 paper, Lemma 2.1, for the elementary grid-vanishing principle. These were read through public-web retrieval; no downloaded byte-certified literature corpus or priority search is claimed. The mathematical arguments used by Report69 are proved in the article. `qa/LITERATURE_CHECK.md` records the exact links and scope.

## Authenticate a received release

Use Python 3.9 or newer. Inspect `tools/release69.py` before running it. Replace `EXPECTED_MANIFEST_SHA256` with the final manifest digest obtained outside the archive. A manifest carried inside an archive does not authenticate itself.

From the release directory:

```sh
python3 -I -S -B tools/release69.py verify \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256
```

Verification checks exact file/directory descendants, regular single-link files, hashes, byte sizes, permission modes and nanosecond modification times, plus the fixed inert-input pin map. Symlinks, special files, unexpected entries and empty directories are rejected. The external digest authenticates the manifest bytes. The manifest's own filesystem metadata and the top-level release root's mode/time are outside that descendant manifest inventory; per-operation snapshots check preservation of the current root. Read-access times are excluded. Creation/change timestamps do not transfer to a new filesystem.

Ordinary ZIP extractors often discard nanosecond times. Use the supplied metadata-preserving extractor from an already inspected copy:

```sh
python3 -I -S -B tools/release69.py extract \
  --archive /absolute/path/to/Report69-source-evidence-20261004.zip \
  --output-dir /absolute/path/to/new-report69-copy \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256
```

Before writing, extraction authenticates the manifest, exact member list, payload bytes and file modes, rejects traversal and nonregular entries, then restores authenticated descendant mtimes. The new root has mode 0700. The manifest itself receives mode 0644 and the fixed epoch. ZIP timestamps, compression choices, comments and other container metadata are not independently authenticated by extraction. The output must not exist and must lie outside the release and protected original trees. Verify the extracted copy again.

## Rebuild into a fresh external directory

Inspect `tools/build_report69.py` and its hash-pinned release helper before execution. The manuscript-map SHA-256 is:

`38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c`

The build-dependency-lock SHA-256 is:

`62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5`

After authenticating the release:

```sh
python3 -I -S -B tools/build_report69.py \
  --output-dir /absolute/path/to/new-report69-build \
  --pins-sha 38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c \
  --dependency-lock-sha 62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5 \
  --require-packaged-match
```

The builder uses a fresh local TeX format, fresh selected font map, allowlisted environment, disabled shell escape, three passes and the union of the format and every pass's recorded inputs. It checks exact PDF equality, preservation and every rendered PNG's dimensions, CRC and raster structure. Visual review remains separate. The output contains PDF/text/logs, all page images, recorder receipts and preservation/build receipts.

The lock covers interpreter and executable bytes, all recorded system TeX/font inputs and selected font maps. It does not inventory shared libraries, Python's standard library or the operating system. A different toolchain should fail preflight rather than be described as identical. The fixed SOURCE_DATE_EPOCH is 1791072000; variable PDF dates and trailer IDs are omitted. The `--bootstrap` option is authoring-only and records an initial dependency set without claiming preflight lock verification.

## Deterministic archives and owned selftests

Create a deterministic archive only from an authenticated release:

```sh
python3 -I -S -B tools/release69.py archive \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256 \
  --output /absolute/path/to/new-report69.zip
```

Creation sorts entries under the fixed `Report69/` prefix, uses one fixed ZIP timestamp, preserves authenticated file modes and applies fixed deflate settings. Repeated creation in the same Python/zlib environment is checked for byte equality. The manifest carries original descendant nanosecond times for the supplied extractor. Do not regenerate the manifest merely to make altered content pass.

The owned synthetic selftest is distinct from independent review:

```sh
python3 -I -S -B tools/selftest69.py \
  --output-dir /absolute/path/to/new-report69-selftest
```

Its 39 passing tests cover valid/rejected pins, output/source alias guards, exact metadata, first-pass-only dependency retention, hostile inherited temporary-directory variables, malformed PNGs, deterministic archives, metadata-preserving extraction, relocated verification and exact PDF reproduction. It uses synthetic TeX and inert source copies; no scientific program is run.

## Attribution

The unchanged Pell source is from mathlib4 revision `ac77769fabe23cb237559e7f56578dbead91499f`, by Mario Carneiro and contributors, under Apache License 2.0. Its source header, license and notice remain in the retained dependency directories. It is an inert theorem dependency, not newly authored Report69 code. Mathematical source packets and their independent audits retain their original scope and provenance.

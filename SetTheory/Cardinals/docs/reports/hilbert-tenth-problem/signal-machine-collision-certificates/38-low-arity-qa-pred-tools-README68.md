# Report 68

## Gaussian fluctuations of encoded gap counts and inverse ranks

4 October 2026. Read `Report68.pdf` for the complete article. `Report68.tex` is matching flattened editable LaTeX; six readable modules are in `manuscript/`.

The article counts all positive integer gap triples with normalized endpoint gaps 1/20+2^(-a)/10 and 1/20+2^(-b)/10. Primitive reduced denominators yield exact floor, digit and shell formulas and slope rho=743/1125. No program, halting predicate or witness tuple enters this count.

For a uniform integer cutoff from 1 through X, the deficit rho*N-A(N) has leading mean (1/2)*(log_2 X)^2 and variance (1637/5400)*(log_2 X)^3, with the proved Gaussian limit. A five-state multiplication-by-five carry chain gives an exact block mean, rational conditional variance, a martingale decomposition, and the sharper complete-block O(m^2) variance remainder. Both a cited martingale CLT application and a direct bounded-increment characteristic-function proof are provided. Aligned prefix mixtures and residue-class moment estimates extend the result to every integer cutoff, with variance remainder O((log X)^(5/2)).

The inverse D_r lists triples by total, repeating each total J(N) times. A common-uniform coupling and uniform short-window bounds give L2 comparison error O((log log(H+3))^2). The inverse deviation has leading mean (1125/1486)*(log_2 H)^2, variance (3069375/4416392)*(log_2 H)^3, and the corresponding Gaussian law. Boundary zero, large moduli, rare carries, first and last tied ranks, and adaptive displacement are handled explicitly. Exact shell subsequences explain why these concentration results coexist with sharp pointwise liminf and limsup envelopes.

The two vector diagrams show the exact carry matrix and the inverse shell/common-uniform coupling. They are analytic illustrations, not empirical evidence. No novelty, priority, local limit, Gaussian convergence-rate, exact all-cutoff variance-polynomial, halting-density, or new dynamical claim is made.

## Included material and mathematical acceptance

- `Report68.pdf`, `Report68.tex`, `manuscript/`: article, standalone source, editable modules and pinned manuscript map
- `science/counting/`, `science/forward/`, `science/inverse/`: complete unchanged source packets and stored evidence
- `science/primitive-provenance/`: complete unchanged historical primitive-initialization packet, included for provenance; its Pell, halting and physical material is not a premise of this article
- `audits/counting/`, `audits/forward-v2/`, `audits/inverse/`: complete accepted independent mathematical audits and their inert exact-arithmetic evidence
- `audits/forward-initial/`: preserved superseded initial audit, retained only as history
- `INPUT_PINS.json`: exact source origins and copied frozen file/directory metadata
- `qa/`: source preservation and manifest checks, predecessor contract, build/render/selftest receipts and independent manuscript/tool reviews
- `tools/`: Report68-owned build, release and synthetic selftest programs
- `RELEASE_MANIFEST.json`: final exact release inventory, authenticated by a digest supplied outside the archive

The forward v2 audit accepts the exact means, constants and theorems with one auxiliary endpoint qualification: the weighted telescoping remainder expression is for m>=1. The manuscript says so explicitly and separately defines R_0=0; the exact block mean already gives mu_0=0. The initial audit is not the controlling disposition. The inverse audit accepts its theorem without correction, with forward Theorem A as its stated mathematical dependency. All theorem constants are unchanged.

The Pollard primary citation was independently checked by the forward audit from the indexed author-hosted statement at Chapter VIII, Section 1, Theorem 1, p.171. The full-PDF opening timed out; no complete downloaded or byte-certified book copy is claimed. The audit's `PRIMARY_SOURCE.md` preserves this distinction. The manuscript also supplies a direct proof of the bounded martingale step.

The scientific programs are inert evidence. Report tools never execute or import them. The stored independent inverse audit records 10,139,416 exact assertions and matching sanitizer evidence; those are prior independent scientific results, not newly executed report checks. No counter interpreter, physical simulator, author/upstream scientific program, source checker, saved schedule search or proof-assistant execution is performed. Typesetting reproducibility does not prove a mathematical theorem.

The complete final 21-page manuscript and all page images passed the independent mathematical-transcription and visual review without a required correction. The accepted dossier is in `qa/manuscript-review/`.

The independent release-tool review passed 91 synthetic/adversarial checks and eight full-candidate operations. Direct and authenticated relocated builds reproduce the PDF and all 21 rendered PNGs exactly; all 270 system dependencies match the external lock. Deterministic archives, metadata-preserving extraction and all 186 original source/audit/predecessor files passed preservation checks. Its accepted dossier is in `qa/release-tool-review/`. The reviewer candidate archive is distinct from this later final seal; its digest must not be used as the final release digest.

## Authenticate a received release

Use Python 3.9 or newer. Inspect `tools/release68.py` before running it. Replace `EXPECTED_MANIFEST_SHA256` with the final digest obtained outside the archive. Merely hashing a manifest found inside the archive does not authenticate it.

From the release directory:

```sh
python3 -I -S -B tools/release68.py verify \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256
```

The tool checks the exact file and directory descendants, regular single-link files, hashes, byte sizes, modes and nanosecond modification times, plus the fixed inert-input pin map. It rejects symlinks, special files, unexpected entries and empty directories. The manifest's bytes are authenticated by the external digest; its own filesystem metadata and the top-level release root's mode/time are outside the manifest inventory. Per-operation snapshots check that the current root is preserved. Read-access timestamps are not integrity evidence. Original creation/change timestamps are not transported to a new filesystem.

Ordinary ZIP extractors often discard nanosecond times. Use the supplied metadata-preserving extractor from an already inspected copy of the tools:

```sh
python3 -I -S -B tools/release68.py extract \
  --archive /absolute/path/to/Report68-source-evidence-20261004.zip \
  --output-dir /absolute/path/to/new-report68-copy \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256
```

Before writing, extraction authenticates the manifest, exact member list, payload bytes and file modes, rejects traversal and nonregular entries, then restores authenticated descendant modification times. The fresh root has mode 0700; the manifest itself receives mode 0644 and the fixed epoch. ZIP timestamps, compression choices, comments and other container metadata are not independently authenticated by extraction. The output must not exist and must lie outside the release and protected source trees. Verify again from the extracted copy.

## Rebuild in a new external directory

Inspect `tools/build_report68.py` and its hash-pinned release helper before execution. The locked build uses a fresh local TeX format, fresh font map, allowlisted environment, disabled shell escape, three passes and the union of format and every pass's recorder inputs. It checks preservation and every rendered PNG's dimensions, CRC and raster structure. Visual review is separate.

The manuscript-pin map SHA-256 is:

`49a8c0433b3903cde25ba83f6d0a1eb997633384b1145ba69325fa5e771b427b`

The dependency-lock SHA-256 is:

`6de1c243674abad6286de4e416088d3c48cd3ba95d4d574cd1a184ef7d0368e4`

After authenticating the release, run:

```sh
python3 -I -S -B tools/build_report68.py \
  --output-dir /absolute/path/to/new-report68-build \
  --pins-sha 49a8c0433b3903cde25ba83f6d0a1eb997633384b1145ba69325fa5e771b427b \
  --dependency-lock-sha 6de1c243674abad6286de4e416088d3c48cd3ba95d4d574cd1a184ef7d0368e4 \
  --require-packaged-match
```

The output contains the PDF, extracted text, full recorder receipts, dependency receipt, all rendered pages, preservation records and build receipt. The PDF must equal the sealed article byte for byte. The lock covers interpreter/executable bytes, recorded system TeX/font inputs and selected maps; it does not inventory shared libraries, Python's standard library or the operating system. A different toolchain should fail preflight rather than be called identical.

The fixed SOURCE_DATE_EPOCH is 1791072000. Variable PDF dates and trailer IDs are omitted. `--bootstrap` is authoring-only: it records a first dependency set and explicitly makes no preflight-lock-verification claim. It is not a substitute for locked replay.

## Deterministic archives and owned selftests

To create an archive from an authenticated release:

```sh
python3 -I -S -B tools/release68.py archive \
  --manifest-sha256 EXPECTED_MANIFEST_SHA256 \
  --output /absolute/path/to/new-report68.zip
```

Creation sorts entries under the fixed `Report68/` prefix, applies one fixed archive timestamp, preserves authenticated file modes and uses deterministic deflate settings. These are creation guarantees; extraction authenticates the payload boundary described above. Original descendant nanosecond times remain in the manifest and are restored by extraction. Repeated creation in the same Python/zlib environment is checked for identical bytes. Do not regenerate the manifest merely to make altered content verify.

The author-owned synthetic selftest is separate from independent review:

```sh
python3 -I -S -B tools/selftest68.py \
  --output-dir /absolute/path/to/new-report68-selftest
```

It exercises correct/rejected pins, source/output alias guards, frozen metadata, first-pass-only dependency retention, hostile inherited temporary variables, corrupt PNGs, deterministic archives, preserving extraction, relocated verification and PDF equality. The completed receipt records 39 passing tests. Its fixtures use synthetic TeX and inert copies of evidence; it executes no scientific programs.

## Retained-source attribution

The historical primitive packet includes unchanged `pell-source.lean` from mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, by Mario Carneiro and contributors under Apache License 2.0. Its source header, license and notice remain in `science/primitive-provenance/dependencies/`. It is inert provenance, not newly authored report software and not a dependency of the arithmetic statistical proofs.

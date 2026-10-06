# Report 133: Unlabeled interval graphs

This reader bundle contains the article, editable TeX source, exact finite mathematical checks, and offline reproducibility utilities. The mathematical checker regenerates its data using only Python's standard library; it does not fetch tables or rely on hidden fixtures. Finite checks support the article's calculations but do not constitute a proof of an asymptotic theorem.

## Exact flat inventory

The bundle contains exactly these eleven regular files, with no subdirectories:

- `report133.pdf`: reader article
- `report133.tex`: complete article source
- `check_math.py`: self-contained mathematical checks
- `verify.py`: closed inventory, hash verification, and normal/optimized mathematical replay
- `output_guard.py`: common outside-bundle, new-only output guards
- `build.py`: two independent, clean, three-pass PDF builds
- `pack.py`: deterministic ZIP creation
- `test_adversarial.py`: selected inventory, output, and mathematical mutation tests, plus extraction/repacking
- `build-environment.txt`: reference toolchain and deterministic settings
- `README.md`: these instructions
- `MANIFEST.sha256`: canonical SHA-256 seal of the other ten files

The verifier's fixed inventory is independent of the names listed in the seal. It rejects every extra or missing file, any directory (even empty), symlink (including the manifest), and special file such as a FIFO. The manifest must contain exactly the ten expected names in sorted order, one lowercase SHA-256 digest, two spaces and a basename per line, with LF line endings and a final newline. Duplicate, omitted, extra, self-referential, unsafe, or noncanonical entries fail.

## Reader commands

Use Python 3.10 or later on a POSIX system supporting `O_NOFOLLOW`. No script installs dependencies, downloads data, uploads files, or changes the supplied bundle during ordinary verification. `-B` is shown explicitly; the scripts also disable bytecode writes before local imports. All correctness and security guards use explicit exceptions and remain active under `python -O`.

From the bundle directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --output /tmp/report133-verification.json
python3 -B check_math.py --output /tmp/report133-math.json
python3 -B -O check_math.py --output /tmp/report133-math-optimized.json
cmp /tmp/report133-math.json /tmp/report133-math-optimized.json
python3 -B test_adversarial.py --output /tmp/report133-adversarial.json
python3 -B -O test_adversarial.py --output /tmp/report133-adversarial-optimized.json
cmp /tmp/report133-adversarial.json /tmp/report133-adversarial-optimized.json
```

Every named output must be NEW, outside the bundle, and have an already existing real parent directory. Existing destinations are never overwritten or merged. All symlink components, including dangling final links and symlink ancestors, are rejected. Paths containing `..` are rejected rather than normalized through possibly linked components. Use new names when rerunning. Output validity is checked before inventory reads, mathematical work, copying, TeX work, or temporary/output writes. Final file creation is exclusive and walks POSIX ancestors without following links. These guards do not sandbox arbitrary modified code or defend against a hostile administrator changing mounts or directories concurrently.

`verify.py` checks the seal, runs `check_math.py` normally and with `-O`, requires identical JSON bytes, and verifies that the bundle is unchanged. `--inventory-only` explicitly omits mathematical replay; it is useful for a quick integrity check and does not establish mathematical correctness. The complete mathematical output is included in ordinary verification JSON.

## Deterministic PDF reconstruction

Install a compatible pdfTeX/LaTeX toolchain, including the packages named in `report133.tex` and standard Computer Modern/Latin Modern font maps. The reference versions are in `build-environment.txt`. Then run:

```sh
python3 -B build.py --output /tmp/report133-build
python3 -B -O build.py --output /tmp/report133-build-optimized
cmp /tmp/report133-build/report133.pdf /tmp/report133-build-optimized/report133.pdf
```

Here `--output` is a NEW DIRECTORY, not a PDF filename. Each command first verifies the sealed bundle and mathematics, then generates a clean format in each of two isolated working directories and runs exactly three `pdflatex` passes per build. It fixes the source epoch, locale and timezone, suppresses volatile PDF dates, trailer IDs and path metadata, and disables shell escape. It rejects overfull boxes, unresolved references/citations and rerun warnings. The two PDF byte streams must match each other and the supplied `report133.pdf`. The output directory contains `report133.pdf` and `build-results.json`; temporary TeX work is removed. A failed attempt may leave its newly claimed output directory, so choose a new name for a retry.

Exact bytes require the compatible TeX engine, packages and fonts used for the reference PDF. A different toolchain may make a mathematically equivalent PDF with different bytes; that is deliberately reported as a mismatch. Reproducibility checks do not replace visual review: render all pages with Poppler or inspect them in a PDF viewer to evaluate layout.

## Deterministic ZIP and fresh extraction

```sh
python3 -B pack.py /tmp/report133-source.zip
mkdir /tmp/report133-unpacked
python3 -m zipfile -e /tmp/report133-source.zip /tmp/report133-unpacked
python3 -B /tmp/report133-unpacked/report133/verify.py
python3 -B /tmp/report133-unpacked/report133/build.py --output /tmp/report133-extracted-build
python3 -B /tmp/report133-unpacked/report133/pack.py /tmp/report133-repacked.zip
cmp /tmp/report133-source.zip /tmp/report133-repacked.zip
```

ZIP member ordering, names, timestamps, file types, permissions and metadata are fixed. The archive uses `ZIP_STORED` intentionally, eliminating compression-library-version dependence. It contains only the eleven public reader files under `report133/`, with no directory entries. `pack.py` performs full mathematical and integrity verification before packaging and uses the verified in-memory bytes.

## Adversarial coverage and its limits

The test suite never edits the delivered bundle. It makes disposable copies, applies each selected mutation before freezing the copy's files and directories read-only, and snapshots every tested copy before and after each command. It also checks that the delivered tree is unchanged. Cleanup changes permissions only on disposable copies. Scratch directories are exclusively claimed under the resolved POSIX temporary root, ignoring `TMPDIR` so it cannot redirect test work into the supplied bundle.

Coverage includes:

- Inventory mutations: missing/changed/extra files, empty/nested directories, file/manifest/dangling symlinks, FIFO, missing/empty seal, wrong/uppercase digest, duplicate/missing/extra/self/unsafe manifest entry, ordering, newline, CRLF and non-ASCII failures
- Output preflight: all five command-line utilities, both Python modes, inside-bundle targets, existing files/directories, final/dangling/ancestor links, a linked alias into the bundle, missing/non-directory parents, and `..`; a deliberately broken input seal ensures the output error happens first
- Mathematical mutations: the Fishburn count at order seven, the finite serial-family graph count, the diagonal identity, and the rational logarithmic normalization, followed by deliberate re-sealing of the copied bundle so that the mathematical checker, rather than an obsolete hash, must reject them
- Positive controls: identical normal/optimized mathematical bytes; fresh ZIP extraction; exact archive inventory and metadata; unchanged copied bundle; byte-identical repacking

Each JSON result lists the exact cases that ran and their total negative invocation count. These are selected adversarial tests, not a claim of exhaustive security testing or independent proof of every article statement. PDF rebuilding is a separate command and is not silently implied by the adversarial result.

## Author-only sealing and trust boundary

`MANIFEST.sha256` is the one deliberate in-bundle write exception. It cannot sensibly hash itself. The author command below exclusively CREATES an ABSENT manifest after checking that all ten payload files are present, regular, and the exact allowed inventory:

```sh
python3 -B verify.py --seal
```

It refuses to replace an existing seal, cannot be combined with `--output` or `--inventory-only`, and does not run the mathematics. A seal attests only the bytes selected by its author. The author must run the full reader checks afterward.

To bootstrap a fresh authoring copy before its PDF exists, place the other nine payload files in that copy, with no manifest, then run:

```sh
python3 -B build.py --author-unsealed --output /tmp/report133-author-build
cp /tmp/report133-author-build/report133.pdf report133.pdf
python3 -B verify.py --seal
python3 -B verify.py
python3 -B test_adversarial.py
```

`--author-unsealed` is a second explicit, temporary validation mode, not a write exception: it still writes exclusively outside the bundle and still checks all file types and the fixed inventory. Only `report133.pdf` and the manifest may be absent, the manifest MUST be absent, and the mathematics runs in both Python modes. Copying the finished PDF into the authoring copy is a deliberate author action outside the utility. Editing an already sealed copy requires deliberately removing its old seal in that separate authoring copy and following this workflow again; reader commands never do this automatically.

Retain a trusted copy of the final ZIP hash or manifest hash separately if later corruption detection matters. Hashes and this unkeyed manifest are not a digital signature and do not authenticate an author. An attacker who replaces the checker, fixed inventory and seal together can construct another internally consistent bundle. Re-sealing changed mathematics is intentionally permitted only as an overt authoring action; the semantic mutation tests demonstrate checks against selected errors even after that action, not protection from wholesale malicious replacement.

# Report156 — Proofs of two conjectures on diagonal partitions

This standalone report proves both Conjecture 5.2 and Conjecture 5.3 in Archibald, Blecher, Elizalde and Knopfmacher, *Subdiagonal and superdiagonal partitions*, Afrika Matematika 36, 77 (2025), DOI 10.1007/s13370-025-01282-0.

All partitions use weakly increasing order. The two target sequences are OEIS A238875 (subdiagonal) and A238873 (superdiagonal).

## Results and precise limits

- Uniform coupling of every nonnegative integer shifted subdiagonal class to the Dyson-rank cumulative count, with error O(1/log n)
- s_0(n)/p(n) = 1/2 + O(1/log n), proving Conjecture 5.3 by an elementary argument using the classical partition estimate
- A separate uniform logistic crossover obtained from the positive-rank Dousse–Mertens theorem
- A Lambert W inverse with growing O(log y/loglog y) localization, plus an explicit nested-log initializer
- Exact Catalan-prefix and bounded-height-prefix finite lower bounds
- liminf log A(n)/sqrt(n) at least sqrt(pi²/3 + 2(log 2)²), proving Conjecture 5.2 by exponential separation from distinct partitions

The last constant is a lower bound, not an exact superdiagonal growth rate or leading equivalent. The fixed-height argument fixes height before taking n to infinity, and only afterward takes the supremum of the resulting bounds. No all-orders expansion is proved for either constrained sequence. The inverse has no adjacent-integer or numerically certified-bracket claim. Asymptotic constants and onset are not numerically supplied.

The 2025 paper's Lemma 5.4 is explicitly credited for its rank-zero no-ones injection; the report extends that map to each fixed rank. Classical partition estimates, Catalan numbers, and the path-graph spectrum are prior inputs. Current bounded source searches found no identical later solution but do not establish first-ever priority.

## Files

- `Report156.pdf`: complete article
- `Report156.tex`: editable, self-contained LaTeX source
- `companion.py`: bounded exact computation and optional noncertifying inverse-model illustration
- `test_companion.py`: mathematical and safe-output regression tests
- `counts.json`: exact p(n), q(n), s_0(n), and A(n) for 0 ≤ n ≤ 200
- `finite_checks.json`: deterministic verification counts and scopes
- `data/oeis_prefixes.json`: attributed numerical prefixes, original source URLs, and retrieval date
- `SOURCE_PROVENANCE.json`: original-source hashes, inspection scope, attribution, and limitations
- `build_pdf.py`, `release_tools.py`: exclusive clean PDF build and common local I/O helpers
- `make_zip.py`, `test_release.py`: fixed-allowlist deterministic packaging and release tests
- `SHA256SUMS`: manifest for every allowlisted payload file except itself

The ZIP includes its manifest. A manifest cannot contain its own digest without a self-reference cycle; the archive digest is supplied separately with the release. Journal PDFs, full OEIS entry text, unrelated reports, working files, and review materials are not bundled.

## Requirements

The companion requires Python 3.10 or later and only the standard library. Safe file publication requires POSIX directory-relative file operations, O_NOFOLLOW/O_DIRECTORY, and hard-link support. No network or third-party Python package is used by the companion or release scripts.

The PDF was built with Python 3.12.14 and pdfTeX 1.40.26 (TeX Live 2025/dev/Debian). Required tools are `pdftex` and `pdflatex`; required packages/fonts are fontenc, Latin Modern, amsmath, amssymb, amsthm, mathtools, geometry, booktabs, longtable, array, microtype, and hyperref. Poppler's `pdfinfo` and `pdftoppm` are useful for visual review but are not used by the builder.

## Exact companion commands

Run from the extracted package root. Output defaults to stdout. To save JSON, use a new `.json` filename in an existing trusted directory:

```sh
python3 -B companion.py counts --max-n 200 --out replay_counts.json
python3 -B companion.py verify --max-n 200 --enumerate-to 40 --prefix-to 10 --out replay_checks.json
cmp counts.json replay_counts.json
cmp finite_checks.json replay_checks.json
python3 -B companion.py threshold --value 1000 --max-n 200
python3 -B companion.py inverse-model --value 1000000000
python3 -B -m unittest -v test_companion
python3 -O -B -m unittest -v test_companion
```

The exact threshold command searches actual subdiagonal counts. It reports failure to find the threshold when the bounded table is too short; it never substitutes an asymptotic estimate. The `inverse-model` command is a floating-point illustration of the smooth model and nested-log initializer. Its output is explicitly noncertifying: it supplies no computable big-O constant, rigorous bracket, or exact integer threshold. Floating-point illustrations need not be byte-identical across platforms; the exact shipped count and verification outputs are deterministic integer JSON.

The integer API rejects booleans and non-integer types. The CLI accepts only canonical nonnegative decimal integers, with no leading zeroes except zero itself. Bounds are n ≤ 200, direct enumeration through n ≤ 40, prefix enumeration through M ≤ 10, and height ≤ 200. The threshold input is at most 10^300; each action enforces its appropriate lower bounds and feasibility conditions. The direct-enumeration range must also fit the requested maximum n; prefix enumeration is independently bounded by 10. These workload limits are software limits, not restrictions on the mathematical theorems.

### Verification coverage

At the shipped settings, independent direct enumeration exhausts 215,308 partitions including the empty partition through n=40. It agrees with the separately structured multiplicity DP. Verification includes 215,267 fixed-rank injection and inverse cases, 446,242 eligible interior-lemma cases at the minimal admissible shift, 860 shifted/rank subset comparisons, 23,714 Catalan prefixes including empty through M=10, 88 bounded-height prefix/walk comparisons, 1,690 Catalan finite lower bounds, 9,995 bounded-height finite lower bounds, and 3,047 disjoint prefix-tail concatenations. The 57/61 supplied diagonal OEIS terms and ordinary/distinct prefixes agree exactly.

All decisions in these finite checks use integers. They support indexing and implementation correctness, not asymptotic onset, the value of an unknown limiting constant, or an exact inverse from a smooth model. Explicit checks remain active under Python `-O`. The companion suite has 37 tests; the release suite has 11 tests, each run normally and with optimization enabled.

### Companion output safety

The companion never overwrites an existing target of any kind. Symlink components, dot/parent traversal, empty or trailing-slash paths, directories, FIFOs, and other special-file destinations are refused. The existing output parent must be owned by the current user and must not be group- or world-writable. A complete private temporary file is linked exclusively to the new target, so the publication is atomic and no-clobber. A failure after the link may leave the complete result present; inspect it rather than blindly retrying or deleting it.

These guarantees assume a trusted environment without a malicious same-user actor modifying the parent or source tree concurrently. Parent descriptor pinning and path rejection reduce accidental path substitution; this is not a general operating-system sandbox.

## Clean PDF replay

Choose two new build directories whose parents already exist:

```sh
python3 -B build_pdf.py --output-dir /tmp/report156-build-one
python3 -B build_pdf.py --output-dir /tmp/report156-build-two
cmp /tmp/report156-build-one/Report156.pdf /tmp/report156-build-two/Report156.pdf
cmp Report156.pdf /tmp/report156-build-one/Report156.pdf
```

The builder creates each directory exclusively, isolates a fresh LaTeX format and cache, disables shell escape, fixes the epoch and PDF metadata, and repeats LaTeX until references stabilize. It rejects warnings and layout diagnostics in the settled log. The `.tex` file is the sole authoring input. Byte identity is expected within the same recorded toolchain; it is not promised across TeX versions, fonts, operating systems, or arbitrary platform changes.

The build destination must have a trusted parent and must not be subject to concurrent adversarial replacement. Existing paths, static symlinks, and parent traversal are refused. The mkdir-then-open step is not claimed to resist a malicious same-user process replacing the just-created directory in that interval. Subsequent operations are descriptor-pinned. TeX is not a sandbox for arbitrarily modified source, even with shell escape disabled.

## Manifest and archive replay

From the unchanged extracted root:

```sh
sha256sum -c SHA256SUMS
python3 -B -m unittest -v test_release
python3 -O -B -m unittest -v test_release
python3 -B make_zip.py --output /tmp/Report156_rebuild_one.zip
python3 -B make_zip.py --output /tmp/Report156_rebuild_two.zip
cmp /tmp/Report156_rebuild_one.zip /tmp/Report156_rebuild_two.zip
```

The packager verifies each payload hash against an exact sorted allowlist, excludes unlisted files, and fixes ZIP timestamps, member order, permissions, and ZIP_STORED compression. Its output is exclusive and never overwrites an existing file, symlink, directory, or special file. A trusted parent and a nonadversarial source tree are required. It does not include itself recursively. Editing the source and issuing a new checksum manifest is a separate authoring/release action; an edited package should fail verification against this original manifest.

No external publication, OEIS editing, author contact, or public repository change is part of this package.

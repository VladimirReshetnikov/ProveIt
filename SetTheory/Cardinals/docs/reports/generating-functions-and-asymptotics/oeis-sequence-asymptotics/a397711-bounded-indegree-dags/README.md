# Report157 — Airy logarithmic asymptotics for bounded indegree labelled DAGs

This standalone report treats OEIS A397711: simple directed acyclic graphs on the labelled vertex set [n], with every indegree at most two. Graphs have unit weight, independently of their number of compatible topological orders.

## Results and precise scope

Let -zeta be the largest real zero of Ai, and kappa = 3 zeta / 2^(1/3). The report proves

    log a_n = 2n log n - n - kappa n^(1/3) + o(n^(1/3)).

Thus a_n = (n²/e)^n exp[-kappa n^(1/3) + o(n^(1/3))] and a_n^(1/n)/n² tends to 1/e. For y = log x and b = y/[2 W_0(y/(2 sqrt(e)))], its threshold inverse satisfies

    min{n >= 1 : a_n >= x}
      = b + kappa b^(1/3)/(2 log b + 1) + o(b^(1/3)/log b).

For every fixed integer c >= 2, the same proof gives

    log a_(n,c) = c n log n - [c - 1 + log((c - 1)!)] n
                 - kappa (c - 1)^(2/3) n^(1/3) + o(n^(1/3)).

The general statement fixes c before n tends to infinity. Its constants and onset may depend on c; no uniformity for growing c is claimed. The inverse has a growing permitted error scale, no eventual exact-rounding claim, and no certified finite-input bracket from the asymptotic model.

These are logarithmic asymptotics, not a ratio equivalent with a known amplitude or power prefactor. The final remainder is not proved to be O(log n), and no all-orders expansion is established. An O(log n) estimate for a separate exact factorial/product factor does not improve the unknown remainder in the excursion partition function.

The proof uses exact sink inclusion-exclusion, Kung–Yan generalized parking identities, and Mallein's established homogeneous killed-walk area estimates. The reciprocal-potential transfer includes the initial layer, explicit fixed interface intervals, all-sufficiently-large-block-length quantifiers, geometric floor errors, and a forced terminal descent. These prior inputs and the Airy mechanism are not claimed as new.

A bounded literature search found no equivalent application for this exact model; this is not exhaustive scholarly priority clearance. Steinsky's 2003 bounded-indegree coding paper remains unread in full, an explicit priority-check limitation.

## Package contents

- `Report157.pdf`: complete 15-page article
- `Report157.tex`: editable, self-contained LaTeX source
- `companion.py`: bounded exact DAG counts and independent finite checks
- `test_companion.py`: mathematical and output-safety regression tests
- `counts.json`: deterministic exact tables
- `finite_checks.json`: verification results and their precise finite scopes
- `data/oeis_prefixes.json`: attributed numerical sequence prefix and source URL
- `SOURCE_PROVENANCE.json`: original-source hashes, inspection scopes, attribution and limitations
- `build_pdf.py`, `release_tools.py`: exclusive clean PDF build and common local I/O helpers
- `make_zip.py`, `test_release.py`: fixed-allowlist deterministic packaging and release tests
- `SHA256SUMS`: sorted SHA-256 manifest for every allowlisted payload except itself

The ZIP includes its manifest. A manifest cannot include its own digest without a self-reference cycle; the archive digest is supplied separately with the release. Full journal articles, full OEIS entry text, research drafts, review records, unlisted files and unrelated reports are excluded.

## Requirements

The exact companion requires Python 3.10 or later and only the standard library. Safe file publication requires POSIX directory-relative operations, O_NOFOLLOW/O_DIRECTORY and hard-link support. Neither the companion nor release helpers access the network or require third-party Python packages.

The PDF was built with Python 3.12.14 and pdfTeX 1.40.26 (TeX Live 2025/dev/Debian). Required executables are `pdftex` and `pdflatex`; packages/fonts include fontenc, Latin Modern, amsmath, amssymb, amsthm, mathtools, geometry, booktabs, longtable, array, microtype and hyperref. Poppler's `pdfinfo` and `pdftoppm` are useful for visual review but are not used by the PDF builder.

## Exact companion replay

Run from the extracted package root. Output defaults to stdout. To save JSON, use a fresh `.json` filename in an existing trusted directory:

```sh
python3 -B companion.py counts --max-n 100 --max-c 5 --out replay_counts.json
python3 -B companion.py verify --max-n 100 --max-c 5 --rational-to 20 --enumerate-to 5 --parking-to 5 --path-to 9 --out replay_checks.json
cmp counts.json replay_counts.json
cmp finite_checks.json replay_checks.json
python3 -B companion.py threshold --value 1000 --c 2 --max-n 100
python3 -B -m unittest -v test_companion
python3 -O -B -m unittest -v test_companion
```

The threshold command searches the actual counts for n >= 1. For example, value 1000 and c=2 gives first_n=5. If the bound is too short, `reached` is false and `first_n` is null; only N_c(value) > max_n is established. The command does not substitute a smooth-model estimate. No floating-point inverse model or asymptotic certification is included.

The integer API rejects booleans and non-integer types. The CLI accepts only canonical nonnegative decimal integers, with no signs, spaces, non-ASCII digits, or leading zeroes except zero itself. Bounds are n <= 100, 1 <= c <= 8, independent occupancy/rational checks through n <= 25, direct graph and parking enumeration through n <= 5, pathwise checks through n <= 9, and threshold values from 1 through 10^1000. Each parking-word enumeration additionally has a cap of 1,100,000 words. Each verification sublimit must fit max_n; omitted CLI sublimits shrink automatically when max_n is smaller than a default. Threshold searches require max_n >= 1.

The shipped tables use c=1,...,5 and n=0,...,100. Shipped verification uses rational checks through n=20, graph and parking enumeration through n=5, and pathwise checks through n=9. It performs:

- 30 direct graph/count comparisons, exhausting 59,810 pair-state assignments
- 30 direct parking/count comparisons, enumerating 3,035,961 preference words
- 105 independent occupancy/Poisson/sink comparisons with exact rational weights
- 34,590 pathwise summation-by-parts checks and 50 Catalan composition-count checks
- 101 rooted-forest formula values, 500 extension/parent-set bound checks, and 404 indegree-monotonicity values
- All 17 supplied A397711 prefix terms

Finite decisions use exact integers and rational numbers. These calculations support the exact formulas and implementation; they do not prove the asymptotic theorem, its onset, its remainder size, or novelty. The companion suite has 34 tests, and the release suite has 11 tests; both run normally and under Python `-O`.

### Companion output safety

The companion never overwrites an existing target of any kind. Symlink components, dot/parent traversal, empty or trailing-slash paths, directories, FIFOs and other special-file destinations are refused. The output parent must already exist, belong to the current user, and not be group- or world-writable. JSON output is capped at 2 MiB; numerical source input is restricted to a regular file of at most 32 KiB with strict parsing.

A complete private temporary file is linked exclusively to the new target, so successful publication is atomic and no-clobber. A failure after the link, such as a directory fsync failure, may leave a complete result present; inspect it rather than blindly retrying or deleting it. Temporary-name creation uses exclusive creation and does not delete a colliding file owned by another operation.

These guarantees assume a trusted environment without a malicious same-user actor concurrently changing the parent or source tree. Descriptor pinning and path validation reduce accidental path substitution; they do not create a general operating-system sandbox.

## Clean PDF replay

Choose new build directories whose parents already exist:

```sh
python3 -B build_pdf.py --output-dir /tmp/report157-build-one
python3 -B build_pdf.py --output-dir /tmp/report157-build-two
cmp /tmp/report157-build-one/Report157.pdf /tmp/report157-build-two/Report157.pdf
cmp Report157.pdf /tmp/report157-build-one/Report157.pdf
```

The builder creates each directory exclusively, isolates a fresh LaTeX format and cache, disables shell escape, fixes the epoch and PDF metadata, and repeats LaTeX until references stabilize. It rejects warnings and layout diagnostics in the settled log. The `.tex` file is its sole authoring input. Byte identity is expected within the same recorded toolchain; it is not promised across TeX versions, fonts, operating systems or arbitrary platform changes.

The build destination must have a trusted parent and must not be subject to concurrent adversarial replacement. Existing paths, static symlinks and parent traversal are refused. The mkdir-then-open step is not claimed to resist a malicious same-user process replacing the just-created directory in that interval. Subsequent operations are descriptor-pinned. TeX is not a sandbox for arbitrarily modified source, even with shell escape disabled.

## Manifest and archive replay

From the unchanged extracted package root:

```sh
sha256sum -c SHA256SUMS
python3 -B -m unittest -v test_release
python3 -O -B -m unittest -v test_release
python3 -B make_zip.py --output /tmp/Report157_rebuild_one.zip
python3 -B make_zip.py --output /tmp/Report157_rebuild_two.zip
cmp /tmp/Report157_rebuild_one.zip /tmp/Report157_rebuild_two.zip
```

The packager verifies payload hashes against an exact sorted allowlist, excludes unlisted files, and fixes ZIP timestamps, member order, permissions and ZIP_STORED compression. Its output is exclusive and does not overwrite an existing file, symlink, directory or special file. A trusted parent and a nonadversarial source tree are required. A failed output write may leave a new incomplete file; inspect that result rather than blindly retrying or deleting it. The archive does not include itself recursively.

Editing the source and issuing a new checksum manifest is a separate authoring/release action. An edited package should fail verification against the original manifest. Release tests exercise refusals, fixed-allowlist verification, tamper detection and deterministic archive construction under ordinary and optimized Python.

No external publication, OEIS editing, author contact or public repository change is part of this package.

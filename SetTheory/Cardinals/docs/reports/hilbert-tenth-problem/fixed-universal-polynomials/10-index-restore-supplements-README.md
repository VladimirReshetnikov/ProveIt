# Separate supplement replay for Research Report 33

This self-contained package supports two separately audited additions:

1. The generalized signed19 algebraic interface permits every integer `d>=1`,
   `B=2^d`, positive odd `b`, nonnegative `K0`, and arbitrary integer paid mask
   ports. The exponent-selection change preserves the main negative-restoration
   existence proof. Arbitrary ports are not thereby declared compiler exports.
2. On the actual fixed compiler slices, the raw29/positive21 equations imply
   the necessary reduction `R=+p` or `R=-p`, even `q`, the displayed negative
   window restrictions, and input index `v=u` or `v=uA`. Neither positivity of
   restored `R` nor existence of a complete negative zero is established there.

The article's sign-free bootstrap/rank argument is an explicitly imported lemma
with its own source and review. This finite checker does not re-prove it.
The original `repro/` suite remains unchanged and is not imported at runtime.

## Portable run

Python 3.9+ and its standard library are sufficient. No installation or network:

```sh
python3 -I -B /path/to/supplements/verify.py
python3 -I -B -O /path/to/supplements/verify.py
python3 -I -B /path/to/supplements/verify.py --replay
```

`--replay` starts normal and optimized isolated Python children from `/`, using
only temporary output files. It reproduces `CHECKS.json` and `REPLAY.json`
byte-for-byte, rejects four modified evidence copies before checker execution,
and checks that the entire package's before/after file-byte hashes agree.
Optional `--output /existing/directory/new-file.json` saves a newly computed
report outside this package. Existing files are never overwritten.

The launcher pins `FROZEN_HASHES.json` by a literal SHA256. Every payload hash
and the exact file inventory pass before the already-verified bytes of
`checks.py` are compiled. The enclosing article manifest must separately pin
`verify.py`, the small trust root. The hash manifest excludes itself and the
launcher, so no self-authentication is claimed. Upstream `.py` files remain
inert bytes; no source schedule is evaluated. All checks use explicit branches
and exceptions, with no Python assert statements. JSON comparison preserves
exact types: booleans differ from integers, and integers differ from floats.
Duplicate JSON keys and nonfinite constants are rejected.

## Reproduced checks

- All 21 source SHA256/Git-blob/byte-length receipts, the five additional source
  receipts, and two JSON `source_sha256` fields matched their cached `.py` files
- 512 generalized initial-exponent CRT/gcd cases, `t=1,...,512`, evenly split
  between even and odd `t`; notably `D0=(-1)^t mod 3`, not uniformly 2
- 128 positive repunit/input contexts, including `d=1` and large odd input offsets
- 7,644 sharpened outer-estimate cases, with rational denominators cleared exactly
- 1,632 toy outer arithmetic cases: 1,206 negative and 426 positive restored values
- 36 odd-q parity cases, 1,056 abstract rank-representative hits, and 42 conditional
  negative-window arithmetic cases
- 82,080 input discriminant congruences at even `A=4,...,78`, with 741 hits for
  `v=u` and 741 for `v=uA`

The exponent cases check the initial selection lemma, not Dirichlet prime
existence or the subsequent density step. The toy outer cases meet selected
arithmetic equations, not every child residual; no valid compiler instance or
complete zero is claimed. The rank and window cases only test conditional
arithmetic consequences. These finite checks corroborate the proof and cannot
replace it.

## Bound proofs and reviews

`evidence/provenance.json` records original relative names, original SHA256,
packaged SHA256, and byte identity. All evidence copies are unchanged.

- Generalized proof: `GENERALIZED-COMPILER-SUPPLEMENT.md`, SHA256
  `69f64c16aed4f9b962ec82553186ffc25cae79cb6808bfe0a3e6136797c0ae60`
- Generalized PASS audit: `GENERALIZED-SUPPLEMENT-AUDIT.md`, SHA256
  `a47c5dcb49947e3580c0ef79a3e3bb9bc292a7d994546f4d363cbd8c13e97b26`
- Raw/positive proof: `RAW-POSITIVE-REDUCTION.snapshot.md`, SHA256
  `0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9`
- Raw/positive PASS audit: `INDEPENDENT-REVIEW.md`, final wording revision SHA256
  `a82ee544ea93efae25ff8b4e60c3cbe01136d5db2273b82e8eee994f222b6656`
- Main proof/audit and sign-free bootstrap proof/review snapshots are also present

The raw audit's final wording revision supersedes an earlier handoff hash while
its reviewed proof snapshot is unchanged. The copied review text mentions its
original checker; that historical checker is deliberately not packaged or run.
`audit_results.json` and `historical-generalized-exponent-checks.json` are inert
historical evidence. Their reported case counts are not represented as rerun by
this suite. Newly reproduced results are exclusively in `CHECKS.json`.

## Source provenance and paths

The 21 original cached files and two manifests are preserved byte-for-byte.
They originate from `VladimirReshetnikov/ProveIt`, commit
`2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`; public pinned URLs and hashes are
in `source_manifest.json`. Source text can retain historical `/tmp` command
paths or upstream execution examples. These are preserved upstream text,
not executable paths used by our authored tools. The tools use only their own
package directory and temporary outputs. Hash checks authenticate consistency
with recorded receipts, not a fresh online repository retrieval.

Files: `verify.py`, `checks.py`, `CHECKS.json`, `REPLAY.json`,
`FROZEN_HASHES.json`, both source manifests, `sources/`, and `evidence/`.

# Report 129

## Main result

For A279556, use (mu, D) = (9, 1); for A279551, use (mu, D) = (8, 1/2).
With S = n^(1/3)(log n)^(2/3) and sigma = (3 pi^2/(2D))^(1/3),

    n log(mu) - log a(n)
      = sigma S + (7 sigma / 3) S loglog(n) / log(n)
        + O(S / log(n)).

All logarithms are natural. This holds through all sufficiently large
integer n, with the actual sequence indexing a(0) = 1. It is not a
coefficient equivalent, does not identify the S/log(n) coefficient,
and gives no effective numerical onset, polynomial prefactor, ratio
asymptotic, or full transseries.

The article includes the complete new quantitative local-root and
anchored-derivative estimates, integrable potential error, shrinking-strip
dual proof, genuine random-clock and likelihood proof, exact integer-time
endpoint treatment, and error ledger. It also proves the refined inverse
threshold and moment/radial derivative consequences, including the moment
term -k loglog(k)/log(k). Those deductions optimize explicit smooth
upper/lower bounds, never an unspecified coefficient remainder.

## Read the proofs

- `report129.pdf` is the new article
- `report129.tex` is its complete editable source
- `earlier-inputs/report127/report127.pdf` is the unchanged proved reference
  for the exact commitment-tree counting model, uniform discrete entrance
  and repair, and global spatial barrier
- The entire earlier Report 127 source and verification package is included,
  unchanged, with its own original closed inventory

The new article reproduces all input statements and their uniformity.
The full proofs of those earlier inputs are in the bundled Report 127,
so the reader bundle is proof-complete without private notes or downloads.
The earlier report's statements that the next term remains open describe
its own earlier scope; the present theorem supersedes that scope statement.

## Finite companion

The new independent finite companion is under `checks/`, with exact input
and reference data under `data/`. Its own README specifies its scope,
strict input schema, bounded ranges, and negative tests. Entry points:

    python3 -B checks/verify.py --output /tmp/report129-checks.json
    python3 -B -O checks/verify.py --output /tmp/report129-checks-opt.json
    python3 -B checks/negative_tests.py --output /tmp/report129-negative.json

Use fresh output paths. The recorded deterministic outputs are
`data/verification_results.json` and `data/negative_results.json`.
Finite identities and bounded path examples cannot prove asymptotic
uniformity, martingale convergence, singular variational minimization,
or infinite tail bounds. The report supplies those analytic arguments.
No sequence fitting is used to determine the 7 sigma/3 coefficient.

## Closed inventory and offline replay

Check the entire package without writing to it:

    python3 -B integrity.py

Changed or missing bytes, extra files or directories, symlinks, and unsafe
inventory paths are rejected. Normal and optimized Python retain the
explicit guards. `test_integrity.py` exercises fourteen named inventory
mutations in both modes. The nested Report 127 inventory is independently
verified by its own tools. Inventories are integrity records relative to
these verifiers, not authenticity signatures against replacement of the
verifier and inventory together.

Full replay, with a fresh result destination outside this directory:

    python3 -B reproduce.py --output /tmp/report129-replay.json

This performs:

1. Strict outer inventory checks
2. New checker and negative tests in normal and optimized Python, comparing
   their exact output bytes with the recorded references
3. Outer inventory mutation tests
4. Two clean Report 129 TeX builds and bytewise comparison with the PDF
5. The unchanged Report 127's full replay, including its own clean builds,
   mathematical/structural mutation tests, fresh extraction, and repack
6. Deterministic Report 129 ZIP construction and fresh extraction
7. All checks and full replays again in that extracted copy
8. Byte-identical repacking and final confirmation that the originals have
   not changed

`--skip-pdf` explicitly omits PDF rebuilds (including the earlier report's)
and records that omission. It is not a full PDF replay.
The full replay keeps temporary and generated products outside this package.
They require no network or downloaded development source.

Build the new report alone:

    python3 -B build.py --output /tmp/report129-rebuilt.pdf

Create a deterministic reader/source ZIP:

    python3 -B repack.py /tmp/report129-reproducibility.zip

The ZIP contains both PDFs, both TeX sources, and all build/check files.
`build.py` builds twice from clean directories and requires byte equality,
no overfull boxes, and no unresolved references/citations. It does not
replace visual review. `build-environment.txt` records the versions used;
different TeX/compression versions can yield equivalent content but
different bytes. TeX dependencies are the ordinary packages listed in
the document preamble. The finite companion uses Python's standard library.

## External mathematical references

The exact combinatorial construction is from Nathan Britt and Nicholas
Beaton, *Completing the enumeration of inversion sequences avoiding
triples of relations*, arXiv:2512.21943v3, 29 September 2026, Sections
3.8-3.9, Lemmas 5-6, and Appendix A. The article lists the precise
succession-law references. No global priority claim is made.

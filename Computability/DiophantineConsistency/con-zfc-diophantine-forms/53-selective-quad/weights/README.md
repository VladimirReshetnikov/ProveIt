# Selective quadratic isolation

This directory supplies one frozen finite encoding, its mathematical proof, and
an independent exact checker. It is not a search-dependent existence claim.

- Input span M = 183, largest target Q = 5190, convolution height H = 5556.
- All 136 weighted source coefficients are reconstructed from the original
  package31 source after replacing each positive variable by x_i + 1.
- All 71,808 possible source-term/padded-pair products are checked.
- The 22 marked output coefficients are exactly twice the 22 source residuals.
- The 136 reversed exponents are distinct; the leading coefficient is 2.
- Only 267 distinct sums occur among the 528 padded pairs. A full B2 property is
  neither true nor needed.

The proof also establishes sparse target padding and the bound S + T < B^5741
before the arithmetic finalizer deduces that b is a power of two. This source
exponent is not a final polynomial degree. The finalizer and complete fixed
compiler-coefficient binding remain separate mathematical dependencies.

## Authoritative files

- `code_v1.json`: sole canonical weight, row-order, and target tuple.
- `section.tex`: source-isolation, coefficient-bound, positivity, sparse-padding,
  and size-bound proofs, suitable for inclusion in the main report.
- `report.tex`, `report.pdf`: standalone version of the proof (five pages).
- `upstream_parent_quartic31.json`: selected original positive-source residuals.
- `upstream_QUADRATIC_TARGETS.json`: pinned package45 cross-check data, not the
  selected coefficient version.
- `SOURCE_PINS.json`: exact current-pin file paths, SHA-256 and Git blob hashes.
- `source_support.json`: all 136 weighted coefficients in explicit sparse form.
- `verify_selective.py`, `verification_v1.json`: checker and exact stdout receipt.
- `test_selective.py`, `TEST_RESULTS.json`: standalone replay, corruption tests,
  and finite regression tests for sparse padding.
- `prepare.py`: optional deterministic regeneration of `source_support.json`
  from the local pinned original source. No sibling package is needed.

The canonical code SHA-256 is
`53cfdccbb252fd3f6ebe87ae0bb9dad8b2fdfc8c6168f668029add30ed339e25`.

The repository pin is `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
Package45 and original package31 have the same supports but not identical
coefficients: package45 shifted row 15 is original shifted row 15 minus
beta * (x_J + 1). The checker verifies that exact distinction and uses the
original package31 coefficients for all formal extraction identities. The
embedded historical source-pin fields in upstream JSON are retained verbatim;
SOURCE_PINS.json records the commit from which these exact bytes were retrieved.

## Replay

From this directory, with standard Python 3 only:

    python3 verify_selective.py > /tmp/selective-verify.json
    cmp /tmp/selective-verify.json verification_v1.json
    python3 test_selective.py > /tmp/selective-tests.json
    cmp /tmp/selective-tests.json TEST_RESULTS.json

Optimized Python (`python3 -O verify_selective.py`) gives byte-identical output.
The self-test also copies the six verification inputs into a fresh temporary
directory and replays there, so it verifies that no optimizer, search binary,
installed third-party Python package, network access, or sibling research tree
is required. Eleven invalid code/source mutations are rejected. The 14,968
small sparse-padding examples are regression tests; the proof in section.tex,
not bounded testing, establishes the lemma for arbitrary sizes.

On a configured TeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

## Optional search history

The `search.cpp`, `targets.py`, and `optimize_joint.py` files explain the finite
search that found the tuple. They and their logs, intermediate weight vectors,
`joint_best.json`, `target_best.json`, and compiled `search` binary are not part
of the proof or replay dependency set. Release packages may omit all of those
intermediate files. The proof makes no claim of global optimality.

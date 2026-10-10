# A Cayley Certificate for the Mixed Gaussian S4 Reduction

A research continuation for Vladimir Reshetnikov's ProveIt project.

**Read:** `article/cayley_s4.pdf` (editable source: `article/cayley_s4.tex`).

## Mathematical results

The manuscript's mixed Gaussian S4 conjecture is proved:

`S4 = (58 g41 + 24 g32)/7 + 19 pi^5/3584 - 2 beta(4) log(2)`,

where `Sp = sum_{n>=0} (-1)^n H_n/(2n+1)^p` and
`gab = Im Li_(a,b)(i,1)` in the strict nested-sum convention.

The proof uses a complete exact rational word certificate: 852 double-shuffle
rows and one Cayley row, whose coefficient is 224. Among the double-shuffle
rows, 123 have one initially divergent factor; their analytic legitimacy is
proved in the article. Two separate exact verifiers pass. No floating-point
period values or relation solver are trusted in the certificate replay.

The article also proves a mixed antisymmetric reduction and general signed
moment bounds for affine harmonic sequences. A new weight-seven S6 identity
has a rational residual enclosure narrower than 3e-299, but is **conjectural**.
A misleading weight-nine S8 candidate is **rigorously refuted** by a rational
interval excluding zero. These statuses must not be conflated.

This is an exact computer-assisted proof, not a Lean/Coq proof-assistant
formalization. No claim is made about arithmetic independence, minimal depth,
all-weight completeness, minimal certificate size, or worldwide priority.
Cayley symmetry, double-shuffle, and Euler acceleration are established tools.

## Reproduce the exact proof and certified arithmetic

Python 3.10+ standard library is sufficient:

```text
python code/verify_s4.py
python code/verify_s4_independent.py
python code/test_kernels.py
python code/verify_receipts.py
```

The last command recomputes all three N=1000 rational interval certificates
and compares their endpoints exactly; it is not a hash-only receipt check.
`verify_receipts.py` also checks the numerical inequalities printed in the paper.

The optional exact search can also regenerate a certificate:

```text
python code/regenerate_s4.py --output data/local_S4_certificate.json
```

The search implementation is not part of the trusted verification kernel;
its output is checked by both independent verifiers.

To run an individual enclosure:

```text
python code/certified_euler.py --p 6 --N 1000 --output data/local_S6_interval.json
```

The rational lower and upper endpoints are authoritative. Display decimal
strings and recorded running times are not proof evidence. Stored endpoints
are outward-rounded, exactly, to denominator 10^350 to keep files compact.

Optional numerical discovery requires `mpmath` (see requirements-optional.txt):

```text
python code/discover_candidates.py --p 6 --dps 110 --tol 1e-95 --output data/local_S6_search.json
```

Any returned vector is only a candidate. A failed search proves no arithmetic
independence. The original 180-digit quadrature files are retained separately
from the exact rational receipts.

## Build the article

Install PDFLaTeX with the packages named in the TeX preamble, then run:

```text
python code/build_article.py
```

The delivered PDF was compiled and rendered for review. Rebuilding can change
binary metadata; a modified PDF requires its own visual review. The manifest
pins the distributed files, not a promise of byte-identical PDF builds.

## Integration and provenance

The inspected repository snapshot is
`a2a4cf58c49c745058c40e4a6748d472a3420f18`.
This is a targeted continuation, not an independently verified audit of the
whole book. See `PROVENANCE.json`, `integration/INTEGRATION.md`, and
`integration/CORRECTIONS.md`. No remote repository files were modified.
The replacement TeX fragment preserves the existing S4 equation labels.

## File map

- `article/`: paper and editable TeX source.
- `data/S4_certificate.json`, `.tsv`: complete exact certificate.
- `code/`: two word verifiers, algebra kernels, rational evaluator, tests, optional discovery, build script.
- `data/*N1000.json`: exact rational numerical enclosures.
- `data/*quadrature*`, `data/*discovery*`: non-certified experiment history.
- `integration/`: replacement manuscript subsection, bibliography entry, targeted corrections.
- `logs/`: executed mathematical checks, build logs, environment and visual-review receipt.
- `MANIFEST.sha256`: hashes of the final distributed files.

Prepared with ChatGPT for review and integration into ProveIt. The supplied
proof data are intended for independent checking and further mathematical review.

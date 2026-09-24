# Nonintegral tropical degree from two horizontal segments

**Main files:** `article.pdf` (18 pages) and its self-contained LaTeX source,
`article.tex`.

## Result

For the strict-witness tropical Hilbert function in Grigoriev's
arXiv:2404.06440v2, with nonnegative integer exponents of total degree at most k,
let

    V_d = ([0,1] × {0}) ∪ ([d+1,d+2] × {1}),    d > 0 rational.

The article proves for every integer k >= 0:

    TH_{V_d}(k) = k + min(k, ceil(k/d)) + 1.

In particular,

    V_3 = ([0,1] × {0}) ∪ ([4,5] × {1}),
    TH_{V_3}(k) = k + ceil(k/3) + 1,
    deg_T(V_3) = 4/3.

This gives proposed negative resolutions of the source's integrality question
and eventual-polynomiality conjecture. The proof is complete in this draft,
but has not been independently refereed or proof-assistant verified. See
`STATUS.md` for precise scope and the limitations of the priority search.

The result generalizes: deg_T(V_d) = 1 + min(1,1/d). Every rational number in
(1,2] is attained. When d = p/q > 1 is reduced, the exact least quasipolynomial
period is p. For d >= 1, the same exact formula also holds for the source's
separate box cutoff, 0 <= i,j <= k.

## Proof in the article

The upper bound orders active integer slopes on the two horizontal components.
Two strict inequalities at the facing endpoints imply d(P-r) < k, and hence
P-r <= ceil(k/d)-1. A separate total-degree argument gives the cap 2k+1.
The lower bound constructs two rows of exponent vectors, one on i+j=k and
one on j=0, and supplies explicit rational coefficients and rational witness
points. Every within-row and cross-row comparison is proved strictly.

The set is explicitly defined by three min-plus equations. No balancing,
ideal-theoretic Hilbert function, irrational exponents, or unproved geometric
representation theorem is assumed.

## Reproduce the exact checks

Python 3.10 or later; standard library only:

```sh
python3 code/verify.py --max-k 40
python3 code/select_area.py
```

The first command regenerates the recorded computational outputs. The second
**audits the retained original random draw without drawing again**. The
original one-based result is entry 50 of 96: Tropical geometry. The default
selection audit also checks that the retained ordered area list matches the
source code. To verify the exclusion-file digest, add:

```sh
python3 code/select_area.py --manifest '/path/to/manifest(1).tex'
```

The user's manifest is not redistributed in this archive. The SHA-256 digest
and an extracted list of its 71 entry titles are retained in
`data/manifest_audit.json`. This records the exclusion input; it is not a
certification of the mathematics of those earlier reports.

A new random selection is optional and separate from the reported research:

```sh
python3 code/select_area.py --new-draw --output new_selection.json
```

Existing records cannot be overwritten by that command. Do not run the
verifiers with Python's `-O` flag: they intentionally reject disabled assertions.

## Recorded checks

The main recorded run tested fourteen rational gaps and every 0 <= k <= 40:
574 parameter–degree cases, 823,974 exact strict witness comparisons (including
the 42 comparisons of the hand-checkable seven-term example), 574 endpoint
upper-bound checks, and 451 box endpoint checks for d >= 1. It also checks the
first 121 generating-function coefficients for d=3.

These are direct rational witness checks and integer endpoint relaxations.
They are not exhaustive searches over all tropical polynomials. The finite
calculations supplement the all-degree proof, not an extrapolation in its place.

## Build the article

A standard TeX Live or equivalent installation with pdfLaTeX, AMS packages,
TikZ, Latin Modern, hyperref, fancyhdr, placeins, and booktabs is sufficient.
There is no external bibliography-processing step.

```sh
make pdf
```

Without `make`, run the following command three times to stabilize the contents
and all cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Package contents

- `article.tex`, `article.pdf`: the full mathematical article.
- `code/verify.py`: exact certificate construction and verification.
- `code/select_area.py`: retained-draw audit and explicit new-draw utility.
- `data/verification.csv`, `data/verification_summary.json`: full recorded tests.
- `data/example_k4_d3.json`, `data/example_gap_matrix.json`: the hand example
  and its complete 100-times-gap matrix.
- `data/certificate_k12_d3.json`: an additional exact certificate.
- `data/hilbert_d3.csv`: H_3(k) for k=0,...,120.
- `data/area_selection.json`, `data/manifest_audit.json`: selection/exclusion audit.
- `notes/sources.md`, `notes/proof_audit.md`, `notes/pdf_validation.md`: source,
  proof, and production checks.
- `STATUS.md`: precisely what is and is not claimed.

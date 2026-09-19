# Ordinal Order Maps and Finitary Powersets of Ordinal–Finite Grids

Research manuscript and reproducible calculations, 19 September 2026.

## Read first

- `ordinal_order_maps.pdf`: the 19-page article, with complete proofs.
- `ordinal_order_maps.tex`: editable, self-contained LaTeX source.
- `STATUS.md`: exact claim scope and unresolved questions.
- `SOURCES.md`: source versions and theorem/question locators.

The published motivation is the extension question in Section 6 of Abriola
et al., *Measuring well-quasi-ordered finitary powersets*, arXiv:2312.14587v2.
This work gives exact maximal-order-type and height calculations for finite
Hoare powersets of an ordinal times an arbitrary finite poset. It is a
partial contribution to that broader open research direction, not a claim
to have completed the whole program. Priority for the formulas has not been
established. The arguments have not been independently refereed or formally
verified.

## Mathematical results

For a finite poset Q and an ordinal beta with repeated Cantor blocks
`beta = omega^gamma_0 + ... + omega^gamma_(m-1)` in descending exponent order,

`o(Mon(Q,beta)) = natural_sum_{s:Q -> m isotone} omega^(natural_sum_q gamma_s(q))`.

The rank of a map is the natural sum of its coordinate values. The finitary
Hoare quotient of `alpha x P` is isomorphic to `Mon(P^op, 1 + alpha)`, with
ordinary ordinal addition in `1 + alpha`. For an infinite alpha, this equals
alpha; for a finite alpha=k, it equals k+1. The empty subset is included.

The ordered-fiber signature of Q counts surjective isotone maps with
specified ordered nonempty fiber sizes. It determines the entire maximal
order type profile. For n=|Q|>0, the single target

`Theta_n = omega^((n+1)^(n-1)) + ... + omega^(n+1) + omega`

encodes the whole signature without exponent collisions. Both the target
and its output lie below omega^omega, although the profile theorem applies
to all ordinal targets.

## Code

Python 3.10 or newer is required. No third-party packages are needed. The
recorded run used Python 3.13.5. Run commands from this directory:

```sh
python code/ordinal_maps.py --demo
python code/ordinal_maps.py data/fork_grid_input.json
python code/ordinal_maps.py data/mixed_exponent_input.json --output data/mixed_exponent_output.json
python code/verify.py
python code/profiles.py
```

Do not use `python -O` for the verification scripts; they rely on assertions
and explicitly reject optimized mode.

### Input format

```json
{
  "n": 3,
  "edges": [[0, 1], [0, 2]],
  "ordinal": {"cnf": [[1, 1], [0, 1]]},
  "mode": "grid"
}
```

The vertices are integers from 0 through n-1. Edges specify strict
comparisons; the code computes their transitive closure and rejects cycles.
Hasse edges or a full transitive relation are both accepted.

- `mode: "grid"` means the input is alpha and P. The answer describes finite
  subsets of alpha x P under Hoare domination, modulo mutual domination.
  Dualization and the conversion to `1 + alpha` occur internally.
- `mode: "maps"` means the input is beta and Q. The answer describes isotone
  maps Q -> beta under pointwise order.

A nonnegative integer encodes a finite ordinal. A nonfinite ordinal uses
`{"cnf": [[exponent, positive_coefficient], ...]}` with recursively encoded
exponents in strictly descending order. For example:

```json
{"cnf": [[{"cnf": [[1, 1], [0, 1]]}, 1]]}
```

encodes omega^(omega+1). Invalid or noncanonical Cantor forms are rejected.

The output contains both human-readable strings and canonical JSON forms.
In strings, `omega*3` means ordinary right multiplication, omega·3, and
`omega^(omega*2 + 2)` is an ordinal power with the indicated exponent.

### Module contents

`code/ordinal_maps.py` implements hereditary Cantor arithmetic, finite
posets, the direct block formula, ideal-chain dynamic programming, the
height formula, and the grid reduction.

`code/profiles.py` implements composition signatures, the universal probe,
probe decoding, signature evaluation, and a separate set of cross-checks.

`code/verify.py` independently enumerates finite map ranks and finite Hoare
quotients and compares the two ordinal calculation methods.

### Explicit limitations

The executable ordinal notation domain is **below epsilon_0**, not all
ordinals. The mathematical proofs have no such bound. The code is
exponential in finite-poset size, and it contains safety limits rather than
a claim of scalability: the ideal DP defaults to at most 18 vertices,
direct enumeration to 2,000,000 candidate assignments, and expanded Cantor
forms to 10,000 blocks. Inputs below those limits can still be expensive.

The DP has at most m*3^n state transitions, but the simple ideal-pair
preprocessing may take O(4^n) subset tests, and symbolic ordinal arithmetic
and expression growth add further costs. No polynomial-time or uniform
bit-complexity bound is claimed.

## Verification artifacts

`data/verification.json` and `.log` record:

- 408 naturally labeled posets with at most five vertices;
- 2,040 finite map spaces and 130,736 independently computed point ranks;
- 2,040 symbolic direct-formula/DP comparisons;
- 153 finite Hoare quotient cases, enumerating 11,483 subsets;
- 400 seeded ordinal-arithmetic triples; no failed assertions.

`data/profile_checks.json` and `.log` record 408 probe decodings, 6,066
signature coefficients, and 2,040 additional signature/DP comparisons, with
no failed assertions.

These are implementation tests, not formal verification of transfinite
mathematics or evidence of literature priority. `data/finite_checks.csv`
contains the individual finite map-space counts and heights.
`data/examples.json` contains the fork, dual fork, chain, and antichain data.

## Build the PDF

With a TeX distribution containing newpx, amsmath, amsthm, microtype, tikz,
tcolorbox, hyperref, cleveref, listings, and the other standard packages
listed in the preamble:

```sh
make pdf
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error
ordinal_order_maps.tex` three times. The bibliography is included directly;
BibTeX and external images are not required.

`make verify` reruns both verification scripts. `make clean` removes only
LaTeX build intermediates, not the PDF, source, code, or recorded data.

No copies of cited papers or standalone font files are distributed.

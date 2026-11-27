# Exact p-adic symplectic corner laws

Research note prepared for Vladimir Reshetnikov, 26 November 2026.

Read `report.pdf`; `report.tex` and `sections/` contain the complete source.
All mathematical results proved in this packet are unconditional.

## Main results

For a Haar symplectic transformation in dimension 2g >= 4, compressed
between two pairing-one symplectic frames, the exact likelihood over a
complete DVR with residue cardinality q is

    h(A) = (1-q^(-(2g-2)))/(1-q^(-2g))
           * sum_{r=0}^{v(1-det A)} q^(-(2g-3)r).

The paper gives the precise finite-ring terminal correction. The total
variation distance from independent uniform entries is

    (1-1/q+1/q^3) * (q^2-1)/(q^(2g)-1)

at every precision, including the complete ring. The event det(A)=1 modulo
the uniformizer is optimal. This preserves the best equal-prior test;
higher digits still change likelihood ratios and can matter for other tests.

Further results include an exact hierarchy for uniform completion after any
precision, the complete nontrivial cokernel law, a sampler with mean 8/5
proposals, an extension to taller corners, and a general rectangular lifting
criterion whose differential defect is binomial(intersection dimension, 2).

## Reproduce

Requirements: Python 3; NumPy for the main exhaustive checks; Matplotlib for
the figure; a standard LaTeX installation with latexmk and BibTeX for the PDF.

```sh
python3 code/verify.py
python3 code/verify_taller.py
python3 code/independent_ring_check.py
python3 code/figures.py
latexmk -pdf report.tex
```

The main verification is exhaustive, not Monte Carlo. It examines
110,894,547 ordered pairs across twelve ring-and-dimension cases, with
20,067 exact output-probability comparisons. Separate checks verify 704
formula parameter triples and all 4,489 ordered subspace pairs in F2^4.
The taller-corner and independent small-ring checks are additional.

An example sampler command:

```sh
python3 code/sample.py --p 2 --g 2 --e 20 --count 5 --seed 0
```

The acceptance test uses exact rational arithmetic. The algorithm's law is
exact given ideal uniform randomness; the CLI uses Python's pseudorandom
generator. A `--quick` option on `verify.py` runs only the smaller cases and
overwrites its results file with those checks.

## Source and novelty scope

Inspected repositories:

- `lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `VladimirReshetnikov/ProveIt`, Article, commit
  `fc9889c80312959aee9893ab21bfc9e741719e88`.

The upstream scope is RH and Dirichlet GRH. No full upstream Lean build or
independent kernel replay was performed in this work. No new Lean theorem
is claimed. The new paper uses a finite-field matrix-counting method from
that program, rather than assuming a stronger unproved global arithmetic
transfer.

The paper attributes prior congruence-lifting methods to Pirani and compares
the result with exact GL corners, additive alternating/Hermitian corners,
Hua measures and full-size symplectic-similitude cokernels. A targeted primary
literature search found no matching exact symplectic-compression theorem;
global priority is not certified. See `provenance/novelty_screen.md`.

`SHA256SUMS` records package file hashes. Validation summaries are in
`results/`; source identities and review scope are in `provenance/`.

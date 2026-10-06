# Report175 exact verification code

This is an original, offline reproducibility package for maximum-density kings
on ordinary `2h` by `2w` boards. Squares are distinguished, kings are
indistinguishable, and neither boundary identification nor symmetry quotienting
is used. It verifies bounded examples; the all-height proof is in `report.tex`
and the report PDF.

## Quick start

Python 3.10 or newer is sufficient. The verifier uses only the standard library.
It does not install packages, access the network, or modify its input data.
Run these commands from this directory:

```sh
python -B verify.py                      # default: h=1,...,4; JSON on stdout
python -B verify.py --text               # same bounded run, readable progress
python -B verify.py --extended           # explicitly opt in to h=1,...,6
python -B verify.py --max-h 2             # smaller bounded run
python -B verify.py --self-test          # arithmetic and rejection checks only
python -B guard_tests.py                 # default run in normal Python and -O
python -B guard_tests.py --extended      # h<=6 in both modes, plus corruption tests
```

`--max-h 5` and `--max-h 6` are rejected unless `--extended` is also supplied.
`--json` remains available as an explicit synonym for the default output mode.
Every failed invariant raises an explicit exception and produces a nonzero exit
status. No proof obligation relies on Python's removable `assert` statement.
The complete verification was also run with `python -S`, which disables site
package initialization. Exact results are identical under normal Python and
`python -O`.

`guard_tests.py` creates and removes its corrupted certificate copies in the
system temporary directory. Neither the ordinary verifier nor the guard tests
write to the source package, so both work with read-only package files.

## Files

- `verify.py`: standard-library exact arithmetic, independent geometric and
  row-mask constructions, certificate checks, and synthetic regression cases
- `regenerate.py`: optional reconstruction of the certificates using an
  already-installed SymPy; tested with SymPy 1.14.0
- `guard_tests.py`: two-mode positive checks and eleven deliberate data
  corruptions rejected in each mode
- `data/certificates.json`: normalized integer coefficient lists for the six
  exact scalar GFs, their factors, all monochromatic-component Gram
  determinants and factors, and exact dominant asymptotic coefficients
- `data/default_results.json`: deterministic successful default `h<=4` output
- `data/verified_results.json`: deterministic successful extended `h<=6` output
- `data/guard_results.json`: successful extended normal/optimized regression
  and corruption-test results
- `data/regeneration_results.txt`: successful full regeneration/comparison log

All polynomial lists use increasing powers: `[1,-3,1]` means `1-3z+z^2`.
The scalar GF is `F_h(z)=sum_{w>=1} P_h(w) z^w`; its numerator has constant
term zero and its denominator has constant term one. Data are read as JSON
integer lists, never executed or passed to a string evaluator. Metadata records
producer, generation method, conventions, and literature URLs.

## What the verifier establishes

For every requested height, it performs all of these exact checks:

1. Independently enumerate the four physical square choices in each fixed
   `2x2` block of a single block-column, reject actual king attacks, and then
   derive the binary-word/threshold labels. Check the bijection and its
   `(h+1)2^h` states.
2. Compare every ordered physical state pair with the threshold transfer rule.
   This includes incomparable binary words and both threshold directions.
3. Reconstruct each monochromatic component incidence matrix with union-find.
   Check `M=E0 E1=X0 C X1^T`, the component dimensions, the zero-one property,
   and both `M=UV` and `G=VU`. Compute `det(I-zM)=det(I-zG)` exactly using
   Faddeev-LeVerrier, with its terminal matrix Cayley-Hamilton identity checked.
4. Verify the diagonal rational resolvent identity as a polynomial matrix
   identity after clearing `det(I-zG)`. No approximate matrix inverses are used.
5. Check every supplied determinant factorization by polynomial multiplication,
   exact irreducibility over the rationals, and the Boolean-rank degree bound.
6. Recompute a sufficient integer sequence from the physical transfer and check
   the entire scalar-GF numerator plus `N` consecutive recurrence residuals,
   where `N=(h+1)2^h`. This is a Cayley-Hamilton certificate, not a finite-prefix
   extrapolation: with recurrence onset `L`, each residual is a fixed scalar
   linear functional of `T^j`, so its first `N` zeros force every subsequent
   residual to vanish. The onset must include both denominator degree and the
   complete numerator transient; no recurrence is propagated backward.
7. Compute the exact polynomial gcd by a primitive pseudo-remainder sequence
   over the integers. Check numerator/denominator coprimality, denominator
   factorization, irreducibility, degree bounds, and exponent bounds.
8. Count all cardinalities with a separate physical-row mask DP, without
   block states or thresholds. Verify its maximum is `hw` and compare its
   maximum-cardinality count with the transfer for every `w=1,...,6`.
9. Remove exactly the double factor `(1-(h+1)z)^2` and use rational evaluation
   and differentiation to verify every supplied `alpha_h` and `beta_h`.

The default checks all 7,584 ordered physical state pairs for `h<=4`, thirty
Gram blocks, four exact GFs, 128 scalar recurrence residuals, and 24 board
counts. The extended run checks 245,152 ordered physical state pairs, 126 Gram
blocks, six GFs, 768 scalar recurrence residuals, and all 36 board counts.
The reduced denominator degrees are `2,4,7,17,31,75`.

The irreducibility test is complete within the explicitly bounded maximum
factor degree four. Degrees two and three use the rational-root theorem.
A root-free reducible quartic must split into integer quadratics by Gauss's
lemma. Any such factor's values at `0,1,-1` divide the corresponding quartic
values; exhaustive integer interpolation checks every candidate. This avoids
probabilistic or floating-point factor claims.

Regression tests include a nilpotent two-state transfer with
`F(z)=2z+z^2` and denominator one. Its recurrence onset must still be two,
so it detects erroneous omission of a zero-eigenvalue polynomial transient.
Corruption guards reject changes to numerator, denominator, onset, factor
exponents, claimed irreducibility, Gram determinant, initial counts, state
count, coefficient normalization/types, and dominant coefficient data.

## Optional regeneration

An existing installation of SymPy is needed only for this separate producer.
The package does not download or install it. No prior calculation scripts or
third-party chess code are imported.

```sh
python -B regenerate.py --compare data/certificates.json
python -B regenerate.py --extended --compare data/certificates.json
python -B regenerate.py --extended --output regenerated_certificates.json
python -B verify.py --extended --data regenerated_certificates.json
```

Default regeneration is bounded at `h<=4`; extended `h<=6` also requires the
explicit flag. Without `--output`, regeneration writes no certificate file.
With `--output`, it creates only the specified new file and rejects an existing file or symlink before computing. The comparison requires
exact equality of every reconstructed mathematical certificate field.

Regeneration builds the full physical transfer and uses its verified Boolean
block triangularity to obtain the full characteristic determinant as the
product of the diagonal determinants. It preserves all `N` possible adjugate
numerator slots, even if zero eigenvalues make the determinant's degree smaller
than `N`, and only then performs exact cancellation. It never uses
Berlekamp-Massey or fitted recurrences. The produced GFs are subsequently checked
by the distinct `N`-residual certificate verifier and the physical-row DP.

Fresh regeneration matches all six earlier exact GFs and all four independently
computed full-characteristic-matrix audit GFs. The standalone package need not
access those earlier working files. It does not replay the earlier audit's full
rational inverse of the complete transfer matrix or its nullity calculations;
the diagonal polynomial inverse identity and scalar certificates listed above
are exactly the checks supplied here.

## Dominant coefficient convention

Write `F_h=P/Q`, let `n=h+1`, and define
`H(z)=P(z)/(Q(z)/(1-nz)^2)`. The exact quantities checked are

```text
alpha_h = H(1/n)
beta_h  = alpha_h - H'(1/n)/n
P_h(w)  = (alpha_h*w + beta_h)*n^w + subdominant terms
```

These are fixed-height quantities. The code does not establish an estimate
uniform in height or a square-board asymptotic. Negative `beta_h` is compatible
with positive counts because the omitted subdominant terms can be important
at small widths. All six rational values appear in the JSON data and output.

## Producer and source provenance

The code and machine-readable certificate representation were newly prepared
for Report175 on 3 October 2026 with OpenAI assistance. The public mathematical
antecedents are credited below; this package does not claim their transfer
construction, leading fixed-height asymptotic, or previously conjectured
factor bounds as newly invented. Historical first-priority questions are
qualified in the report.

- Donald E. Knuth, *Non-attacking Kings on a Chessboard* (1994):
  https://www-cs-faculty.stanford.edu/~knuth/papers/nkc.tex
- Herbert S. Wilf, *The Problem of the Kings*, EJC 2 (1995), R3:
  https://doi.org/10.37236/1197
- Vaclav Kotesovec, *Non-attacking Chess Pieces*, sixth edition (2013),
  especially p.83: http://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf
- Tricia Muldoon Brown, *Maximum arrangements of nonattacking kings on the
  2n x 2n chessboard*, published 2025:
  https://doi.org/10.2478/rmm-2025-0003
  (preprint: https://arxiv.org/abs/2111.10331)

These are references, not bundled third-party materials. No book, journal PDF,
Knuth source file, external implementation, or research working notes are
included in this code package.

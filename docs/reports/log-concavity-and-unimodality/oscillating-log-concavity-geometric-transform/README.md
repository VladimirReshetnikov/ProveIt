# Oscillating Log-Concavity in Geometric Generating Functions

Research manuscript and reproducibility package, 19 September 2026.
Prepared for Vladimir Reshetnikov with ChatGPT.

## Main results

The 19-page manuscript gives proofs of the assertions posed as Challenges 2
and 3 in Heim and Neuhauser, arXiv:2302.13327v1, Section 3. The target is the
**geometric** transform `1 / (1 - u G(z))`, not the exponential/product transform.

For divisor-sum weights, every real exponent and every positive `u` give
infinitely many strict log-concavity and strict log-convexity indices, both
with eventually bounded gaps. For integer power weights, all exponents at
least two have the same property. Exponents zero and one have the explicit
eventually log-linear and strictly log-concave behavior stated in the article.

For square weights with `u = 1`, the adjacent determinant is never zero;
every four consecutive positive indices contain both signs; and each sign
has density one-half within every arithmetic progression. The four-index
bound is sharp. The sequence is A033453 with the indexing adjustment
`a[0] = 1`, `a[n] = A033453(n-1)` for `n >= 1`.

A general subdominant-pole theorem is the common mechanism. The square
case also has an exact third-order determinant recurrence, a Galois-theoretic
irrational-angle proof, and an elementary four-point circle argument.

## Files

- `article.pdf`, `article.tex`: complete manuscript and editable LaTeX source.
- `verify.py`: Python 3.9+ exact checks; standard library only; no network access.
- `numeric_square.py`: optional high-precision illustrations, requiring mpmath.
- `verification-output.txt`: output from the default exact verification run.
- `data/`: exact initial terms and signs, counts, rational certificates, and
  optional approximate root/amplitude constants.
- `build.sh`, `build.ps1`: rebuild the verification data and the PDF.
- `STATUS.md`: source/version audit and the boundaries of the novelty claim.

## Run

```text
python verify.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On Windows with PowerShell, `./build.ps1` runs these steps and checks their
exit codes. On a Unix-like system, use `bash build.sh`. A standard TeX Live
installation containing the packages in the preamble is sufficient.
No font files or third-party papers are included.

The default exact run classifies `Delta_1` through `Delta_100000`, with
50,000 positive, 50,000 negative, and no zero determinants. Independent
convolution and rational coefficient extraction agree through `a_601`;
direct determinants agree with the determinant recurrence through
`Delta_600`. All included finite checks passed.

For a smaller run:

```text
python verify.py --limit 10000
```

The optional numerical script is separate:

```text
python numeric_square.py --digits 60
```

It was tested with mpmath 1.3.0. Its decimal output is not a certified
interval computation and is not used to prove any theorem.

## Data conventions

`data/square_signs.txt` has 100,000 ASCII characters followed by a newline.
The first character is the sign of `Delta_1`; `+` is strict log-concavity
and `-` is strict log-convexity. There are no zero characters.

`data/square_initial_terms.csv` contains `n, a_n, Delta_n` for `1 <= n <= 50`.
All entries are exact integers. `square_arithmetic_progressions.csv` reports
finite counts for every residue class of every modulus from 1 through 12;
fractions in the final column are approximate displays of those counts.

`data/lambert_certificates_exact.json` contains exact rational partial sums
and absolute tail bounds certifying `L_d(-9/10) > 1` for `d = 0..10`.
The corresponding CSV is a rounded display, not the certificate itself.

`data/family_comparison.csv` contains exact determinant-sign counts through
index 500 for both families with exponents 0 through 8 and `u = 1`.
`data/square_constants.json` contains optional approximate numerical values.

## Proof and priority status

The manuscript contains conventional proofs; finite tests are supporting
checks rather than proofs of infinitude, bounded gaps, or density. It has
not been independently peer reviewed or formalized in a proof assistant.

A targeted current search found the challenges explicitly stated in the
inspected 2023 arXiv version and did not locate a prior resolution. This
is not an exhaustive certification of priority. In particular, the revised
publisher full text was not available for direct version comparison.
The known OEIS generating function and recurrence are credited as background.
See `STATUS.md` and Section 8 of the article for the source audit.

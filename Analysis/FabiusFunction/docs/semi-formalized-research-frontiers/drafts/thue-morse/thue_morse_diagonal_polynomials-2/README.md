# Diagonal Polynomial Laws in Odd Iterated Thue–Morse Summation

This archive contains the complete source and rendered article requested for
the two-dimensional table defined by odd iterated prefix summation of the
signed Thue–Morse sequence.

## Files

- `thue_morse_diagonal_polynomials.tex` — complete LaTeX article.
- `thue_morse_diagonal_polynomials.pdf` — rendered 37-page A4 article.
- `diagonal_polynomials.wl` — exact Wolfram Language implementation.
- `diagonal_polynomials.py` — exact SymPy implementation and regression suite.
- `VERIFICATION.txt` — commands, versions, and verification results.
- `SHA256SUMS` — checksums of all other distributed files.

## Principal formula

For the diagonal `k = n + d`, `d >= 1`, the article proves

```text
s(n,n+d) = Sum[(-1)^ThueMorse[q] (2n)^(overline(d-1-2q))/(d-1-2q)!,
                 {q,0,Floor[(d-1)/2]}].
```

It is an exact polynomial of degree `d-1` in `n`, with leading coefficient
`2^(d-1)/(d-1)!`.  No interpolation or numerical recognition is involved.

The article also develops the Riordan-array representation, a 2-adic
Newton–Bell recurrence, Sheffer lowering and translation laws, finite block
symmetry and plateaux, exact denominator and rational-root theorems, and an
`O(n^2 log m)` random-access evaluator based on signed Thue–Morse prefix
moments.

## Reproduction

With Python and SymPy installed:

```bash
python diagonal_polynomials.py --max-degree 16 --verify
python diagonal_polynomials.py --max-degree 0 --scan-negative-half \
  --scan-max-b 63 --scan-max-m 10000
```

With a TeX Live installation containing `latexmk`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  thue_morse_diagonal_polynomials.tex
```

In Wolfram Language, evaluate `Get["diagonal_polynomials.wl"]`, then use, for
example:

```wl
Factor[DiagonalPolynomial[12, x]]
SClosed[20, 10^9]
VerifyDiagonalCode[10]
```

The Wolfram source was statically checked for balanced nested comments,
strings, and delimiters.  A Wolfram runtime was not available in the build
environment, so its included self-test was not executed there.  The
independent Python implementation exercised the same formulas exactly.

# Factorial Transseries for OEIS A006014

This archive contains a 22-page research note on OEIS A006014, the sequence

```
1, 2, 7, 32, 178, 1160, 8653, ...
```

defined by

```
a(1) = 1,
a(n+1) = (n+1) a(n) + sum_{k=1}^{n-1} a(k) a(n-k).
```

## Status

AI-assisted research note prepared for Vladimir Reshetnikov on 1 October 2026.
The note is unrefereed. The elementary leading-asymptotic proof and exact
identities are self-contained; the all-orders theorem is also derived by an
endpoint recurrence, with the Borel analysis providing an independent
structural explanation. Independent review is recommended before an OEIS or
journal submission.

## Main results

1. Exact formal hypergeometric linearization:

   ```
   A(x) = x d/dx log U(x),
   U(x) = 2F0((1+i sqrt(3))/2, (1-i sqrt(3))/2 ;; x).
   ```

2. Exact bridge to OEIS A130032:

   ```
   n! [x^n] U(x) = A130032(n).
   ```

3. Elementary proof of the OEIS factorial estimate:

   ```
   a(n)/n! -> cosh(pi sqrt(3)/2)/pi.
   ```

   The proof also gives monotonicity and explicit global error bounds.

4. An all-orders factorial expansion with an exact rational coefficient
   generator, a full rank-one transseries family, and an explicit Stokes jump.

5. A Lambert-W inverse expansion for recovering the index from a large value.

6. A positive one-parameter deformation with the same hypergeometric
   mechanism, proposed OEIS update text, and twelve further research questions.

## Files

- `article.tex` - complete LaTeX source.
- `article.pdf` - compiled 22-page article.
- `verify.py` - exact and high-precision verification script.
- `verification_output.txt` - recorded verification run and numerical tables.
- `oeis_update_draft.txt` - concise proposed OEIS formula/comment and cross-reference text.
- `requirements.txt` - Python packages used by `verify.py`.
- `SHA256SUMS.txt` - checksums for the archive payload, excluding the checksum file itself.

## Build

With a recent TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The document uses standard TeX Live packages, including `newpxtext`,
`newpxmath`, `tcolorbox`, `booktabs`, `hyperref`, and `listings`.

## Verification

```sh
python -m pip install -r requirements.txt
python verify.py
```

The recorded run checks:

- the A006014 recurrence, hypergeometric carrier, A130032 bridge, and triangular
  identity through `n = 80`;
- the late-term coefficients by two independent triangular recursions;
- every displayed normalized, logarithmic, centered, and lambda-deformed
  coefficient;
- monotonicity and the explicit global inequalities through `n = 500`;
- the numerical convergence and inverse tables at 80-digit precision.

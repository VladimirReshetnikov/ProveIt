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

(Editorial, 2026-10-01: the inverse of item 5 is a case of the inversion
apparatus of the canonical transseries volume, which the article does not
cite; an editorial note in the article now cites it. The recorded `PASS`
lines of `verification_output.txt` are fixed text, and the program's
symbolic stage takes minutes; see "Verification". See also the amendments
below.)

## Files

- `article.tex` - complete LaTeX source.
- `article.pdf` - compiled 22-page article (rebuilt from the amended source
  on 2026-10-01; 22 pages as delivered).
- `verify.py` - exact and high-precision verification script (since the
  editorial pass it writes into `rerun/` by default).
- `verification_output.txt` - recorded verification run and numerical tables.
- `oeis_update_draft.txt` - concise proposed OEIS formula/comment and cross-reference text.
- `requirements.txt` - Python packages used by `verify.py`.

The delivered checksum ledger `SHA256SUMS.txt` was verified in full on filing
(batch 73, 7/7) and not kept; the delivered archive remains in the repository
history (see `docs/incoming/README.md`, batch 73 row).

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

The program now writes its tables to `rerun/verification_output.txt` by
default, so the recorded file stays unchanged; only an explicit
`--output verification_output.txt` (from the package directory) overwrites it,
as the delivered default did. `rerun/` is not ignored, so delete it afterwards.
In this repository, on Windows, use
`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify.py`;
bare `python` may not resolve.

**Running time.** The symbolic stage, `verify_symbolic_expansions()`, takes
minutes, not seconds: on filing (2026-10-01) it did not finish within
170 seconds in two attempts and was not run to completion, so allow more than
three minutes for a full run. The other stages together take under a second.

The recorded run checks:

- the A006014 recurrence, hypergeometric carrier, A130032 bridge, and triangular
  identity through `n = 80`;
- the late-term coefficients by two independent triangular recursions;
- every displayed normalized, logarithmic, centered, and lambda-deformed
  coefficient;
- monotonicity and the explicit global inequalities through `n = 500`;
- the numerical convergence and inverse tables at 80-digit precision.

**What the recorded file shows (editorial, 2026-10-01).** The four `PASS:`
lines at the head of `verification_output.txt` are fixed text that
`write_tables` writes before the tables, not results returned by the checks.
`main()` calls `write_tables` only after every check has passed, so a file
written by a complete run is evidence for them, but the file by itself does not
show that the run that wrote it was complete. In particular it is not evidence
that the symbolic stage ran: the second and third lines (the "direct endpoint
recursion" and the normalized, logarithmic, centered and lambda expansions)
name checks of that stage. On a copy on filing, the exact identities through
`n = 80`, the numeric bounds through `n = 500`, the asserted list
`phi_0, ..., phi_11` and the tables passed, and `write_tables` reproduced the
recorded file up to line endings; the symbolic stage was not run to
completion. In the editorial pass the amended program, run with the symbolic
stage skipped, reproduced `verification_output.txt` byte for byte, and every
coefficient list that the symbolic stage asserts (the endpoint recursion for
`m <= 14`, the normalized, logarithmic and centered expansions, and the first
five lambda-deformed coefficients) was reproduced by an independent exact
computation in rational arithmetic, which takes well under a second. The
recorded file is kept as delivered.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 73 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-01)`, every change to the program `ed. (2026-10-01)`. The
author line and PDF metadata name OpenAI and the addressee; they are kept as
delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-10-01)" is defined in the preamble (the theorem counter is unchanged).
  One note, at the end of Section 6 ("Asymptotic inversion"), after the
  delivered sentence on "the inverse-gamma and power--log transseries
  elsewhere in ProveIt", which names no result. It cites the canonical volume
  `../Transseries_And_Inversion/transseries_and_inversion.tex`: the variables
  `X, w, M, q` are its `R, w, T, Lambda` of Section Q.5 (`p6:sec:gamma`), and
  `M(log M - 1) = X` is its factorial core (Proposition J.27,
  `p0:prop:factorial-core`, with `kappa = 1`, `d = -1`); for `a_n = C n!` the
  article's reversion gives `M - 1/2 + d_1/M + d_3/M^3 + ...` of Theorem Q.25
  (`p6:thm:gamma`) and Proposition Q.26 (`p6:prop:gamma-blocks`), and the
  factor `1 - 2/n - 2/n^3 - ...` turns `1/24` into `49/24`, adds the
  `M^{-2}` term and changes the cubic coefficient (both reversions repeated
  by the editors); the general reversion is Theorem J.21
  (`p0:thm:perturbed-inversion`) of the volume's Part X "Inversion: the
  apparatus for a rapidly growing function" (`p0:sec:top`); the step from
  `nu(Y)` to the integer threshold is Theorem J.43 (`p0:thm:staircase`);
  and the volume's chapter "The subfactorial" (`p8:sec:top`) treats its other
  factorially growing sequence, citing the gamma carrier (Proposition S.10,
  `p8:prop:carrier`). The method is the volume's; the A006014 coefficients
  are new to the repository. One bibliography entry, `ed:tai`, is added after
  the delivered ones, so no reference is renumbered. No label was renamed or
  removed.
- `article.pdf`: rebuilt from the amended source by three `pdflatex` passes
  (MiKTeX pdfTeX 1.40.29): 22 pages, as delivered; no error, overfull box,
  undefined reference, multiply defined label or duplicate destination, and
  the four underfull boxes of the delivered build (in the proof-audit table)
  and no other; every font is embedded and none is Type 3. Every theorem,
  equation, table and section number is unchanged (checked against the
  `.aux` of a build of the delivered source). The pages carrying the note and
  the bibliography were rendered and inspected.
- `verify.py`: the new `--output` option defaults to
  `rerun/verification_output.txt` beside the program (as delivered, the
  program always overwrote `verification_output.txt` beside itself), and the
  file is written with LF line endings on every platform (as delivered, the
  platform's, so CRLF on Windows). The checks, the tables and the `PASS`
  lines are unchanged.
- `README.md`: the pointer under "Main results", the file list, the retired
  ledger, the output location, Windows command and running time, the account
  of what the recorded file shows, and this section.
- Recorded, not changed: `verification_output.txt` and its fixed `PASS` lines
  (see "Verification"); the version floors of `requirements.txt` (the
  filing check used sympy 1.14.0 and mpmath 1.3.0).

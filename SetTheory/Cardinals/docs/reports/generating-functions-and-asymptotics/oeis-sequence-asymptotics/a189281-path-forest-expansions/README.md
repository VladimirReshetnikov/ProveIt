# Unconditional all-orders asymptotics for two OEIS permutation sequences

Prepared for Vladimir Reshetnikov, 1 October 2026.

Start with **article.pdf** (21 pages). Its self-contained source is **article.tex**;
no external bibliography, figure files, or nonstandard fonts are needed.

## Scope and status

The report studies A189281 (signed distance-two avoidance) and A110128
(absolute distance-two avoidance), and generalizes them to every fixed pair
of positive offsets. It supplies mathematical proofs of:

- an exact stabilization formula for path-forest tilings and factorial moments;
- a recurrence-independent, all-orders expansion with a uniform complex-variable
  remainder and a finite formula for each correction polynomial;
- whole-distribution Poisson corrections, a factorial denominator bound,
  and a quantitative total-variation universality theorem;
- an all-orders Lambert-W index inversion with a discrete-sequence interpretation.

The article derives and tabulates the two avoidance expansions through n^-16.
The coefficient formula does not use fitted sequence values or a guessed
recurrence. It extends the higher expansions currently displayed by OEIS.

**Not claimed:** a proof of either specific guessed OEIS recurrence, all-orders
integrality for A189281, a complete exponentially improved transseries, a
Lean-checked formalization, peer review, or established historical priority
beyond the sources reviewed. Section 11's rational-collapse formula is a
**conjecture**, tested symbolically only for h=4,...,16. Those finite tests
are not its proof. The existing exact inclusion-exclusion framework is credited
to Spahn and Zeilberger; the report reproves what it uses.

The mathematical proofs and the finite computational checks serve different
purposes. The checks detect implementation and transcription errors; they do
not replace the infinite arguments. Independent mathematical review remains
appropriate before publication or an OEIS update.

## Files

- `article.tex`, `article.pdf`: full article, including eight follow-up research
  topics, proof-dependency audit, and references.
- `code/path_forests.py`: exact coefficient formula, stable moments, and an
  independent full path-tiling enumeration. Standard library only.
- `code/validate.py`: independent brute-force distributions, published sequence
  values, stabilization tests, degree tests, and coefficient regression.
- `code/certify.py`: exact rational Bonferroni enclosures and scaled asymptotic
  residual certificates. Decimal displays are rounded outwards.
- `code/check_collapse.py`: finite symbolic tests of the unproved rational
  collapse. Requires SymPy.
- `code/inverse.py`: numerical inverse diagnostics from exact enumerated inputs.
  Requires mpmath. These are not certified integer-threshold computations.
- `data/coefficients_order16.json`: exact rational coefficients; keys `1` and `2`
  denote the signed and absolute cases. `B[J]` lists coefficients in ascending
  powers of u; `c[J] = B[J](-1)`. Fractions are stored as strings.
- `data/exact_values.json`: n=0,...,21 for both sequences, recomputed by full
  tiling enumeration and compared to the OEIS entries.
- `data/validation.json`, `data/validation.txt`: counts and outcomes of checks.
- `data/bonferroni_certificates.json`: exact rational endpoints, with the stated
  truncation order and cutoff. `scaled_error_*` encloses
  n^(M+1) (exp(theta) A(n)/n! - sum(j=0..M) c[j]/n^j).
- `data/bonferroni_certificates.txt`, `data/inverse_diagnostics.txt`,
  `data/collapse_checks.txt`: human-readable outputs.
- `SOURCES.md`: source and status audit.
- `requirements-optional.txt`: tested versions of the two optional dependencies.
- `build.sh`: compilation helper.
- `SHA256SUMS`: checksums of the delivered files, excluding itself.

## Reproduce the exact computations

Run from this directory, without Python's `-O` flag (the checks use assertions):

```sh
python code/path_forests.py --order 16 --output data/coefficients_order16.json
python code/validate.py > data/validation.txt
python code/certify.py > data/bonferroni_certificates.txt
```

These programs need only Python's standard library. They were tested with
CPython 3.13.5. Their syntax requires Python 3.10 or later; other versions were
not separately tested. The coefficient-generation CLI accepts other fixed
positive offsets, for example:

```sh
python code/path_forests.py --r 2 --s 3 --order 8 --output offsets_2_3.json
```

The direct full-tiling enumerator is intended for independent small-n checks,
not as a replacement for the fastest known large-n counting algorithms.
The stable-moment routine rejects cutoffs outside its proved sufficient range.
No network access is required by any included program.

The recorded checks passed:

- 44 published sequence values (n=0,...,21, both sequences);
- 96 full brute-force distributions (n=1,...,8; six offset pairs; both statistics);
- 246 factorial-moment equalities and 86 unequal-path stabilization identities;
- 375 finite-difference degree checks and 396 coefficient-denominator checks.

The exact interval computations use moment cutoffs 30 and 31 at n=80,160,320.
The full rational endpoints, not just displayed decimals, are the certificates.

## Optional symbolic and numerical checks

```sh
python -m pip install -r requirements-optional.txt
python code/check_collapse.py > data/collapse_checks.txt
python code/inverse.py > data/inverse_diagnostics.txt
```

SymPy 1.14.0 and mpmath 1.3.0 were tested. The symbolic checks prove the individual
rational-function identities in their finite range only. The inverse diagnostics
use 80-decimal working precision, but are not interval certificates.

## Build the PDF

With a TeX installation including the standard packages listed in the preamble:

```sh
sh build.sh
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.
The delivered PDF was built with pdfTeX 1.40.26 (TeX Live 2025/dev/Debian),
checked for unresolved references and overflow warnings, and visually inspected
after rendering all 21 pages with `pdftoppm`.

The build script keeps temporary TeX files in `build/` and copies the completed
PDF to the top level. Rerunning computations or rebuilding the PDF changes
file checksums; `SHA256SUMS` describes the delivered snapshot.

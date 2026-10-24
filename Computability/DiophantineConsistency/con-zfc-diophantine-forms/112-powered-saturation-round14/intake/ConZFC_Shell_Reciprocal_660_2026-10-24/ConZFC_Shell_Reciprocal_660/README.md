# Square-shell syntax and reciprocal-factorial CRT

## Result

The principal artifact is the explicit ordinary quartic polynomial

\[
P_{660}(z_1,\ldots,z_{660})=\sum_{i=1}^{386}R_i(z)^2
\]

over **unrestricted integers**. The complete quadratic residuals are listed
in `report.pdf` and `equations/integer660/equation.json`; the fully expanded
polynomial is `equations/integer660/expanded_polynomial.json`.

The ordinary proof, formalizable in ZFC, establishes

\[
\mathrm{ZFC}\vdash
\bigl[\forall z\in\mathbb Z^{660},\ P_{660}(z)\ne0\bigr]
\Longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The construction uses the repository's direct C222 proof calculus. It
does not encode K215 or invoke a Jones universal polynomial. Its exact
polynomial contains no unspecified parameter or native program payload.

| Form | Domain | Variables | Degree | Residuals | Collected monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Main shell/reciprocal/sign form | integers | 660 | 4 | 386 | 6,408 | 3,877,579 |
| Shell/reciprocal companion | nonnegative integers | 364 | 4 | 292 | 6,613 | 7,002,666 |
| Old-syntax/reciprocal companion | nonnegative integers | 363 | 4 | 291 | 6,674 | 83,842,716 |
| Inspected direct integer baseline | integers | 888 | 4 | 470 | 10,156 | 2,445,790,974,704 |
| Inspected direct natural baseline | nonnegative integers | 407 | 4 | 323 | 8,420 | 83,843,774 |

Height means the maximum absolute coefficient after the single polynomial
has been fully expanded and equal monomials collected. The integer result
removes 228 variables and 3,748 monomials from the inspected direct baseline.
This is not a claim of global minimality, a fewest-variable record, or
worldwide priority. Other repository routes achieve smaller variable counts
with different degree, coefficient, native-payload, and proof-audit tradeoffs.

## Main ideas

1. With `s=x+y`, use the complete four-constructor numbering
   `I=2(s²+x)`, `M=I+1`, `A=2(s²+3x+4y+3)`, `E=A+1`.
   Two complementary square-shell intervals partition the naturals.
   A recursive bijection transports every old numerical derivation while
   fixing truth zero and falsity one, including variable and binder labels.

2. For `F=H!`, use pairwise-coprime moduli `D_i=1+F²/i`.
   Their product is exactly `B=binom(F²+t,t)`, and
   `C=B-F²-1` is the canonical row index modulo every `D_i`.
   Soundness decodes a row modulo one prime divisor of its modulus;
   completeness uses CRT modulo the full moduli. This avoids an incorrect
   composite-modulus root inference.

3. Use the proposed factorial in its own radius `rho=F H²` and use
   `q=B((rho+1)^H+1)` as a common radix. The ceiling identity proves
   `F=H!`, and the low-digit bounds are validated in a noncircular order.

4. Use `W=2+sum(power_port²)` to bound absolute values of proposed power
   outputs. A Pell frame makes the relevant congruence modulus larger
   than the full signed error interval. Ordered sign proofs leave 101
   guards; 636 exact monic eliminations then give the 660-variable form.

## Proof and audit boundary

The inherited logical calibration is
`KEndpoint.c222_iff_zf_refutation` followed by
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The Pell index representation is inherited through
`PellRepresentation.criterion_iff_pell`. Source pins and the relevant
calibration excerpts are included. New proofs are in the report and `proofs/`.

The contribution supplies an ordinary mathematical proof formalizable in
ZFC and independent finite checks of the instantiated arithmetic objects.
It does **not** claim a newly emitted object-language ZFC derivation or a
new end-to-end Lean/Rocq kernel check. The full transitive Lean dependency
closure is not bundled. Finite fixtures do not replace the unbounded
recoding, Pell, CRT, or factorial arguments.

The result establishes an equivalence with consistency, not consistency
itself. Under consistency of ZFC, the no-zero statement is unprovable in
ZFC by the second incompleteness theorem. No stronger two-sided
independence claim is inferred from consistency alone.

## Reproduce and verify

The arithmetic build and checks were tested with Python 3.12 and use only
the standard library. From this directory:

```sh
python3 verify.py
python3 -O verify.py
python3 code/build_release.py --output /path/to/new-empty-directory
```

The default verifier independently authenticates the inherited pins,
binds each raw gate ledger to its exported source, checks all arithmetic
interfaces, replays natural and integer projections, verifies the ordered
sign proof and retained guards, expands the complete sum of squares,
runs deliberate corruption controls, and rebuilds all equation files in
a temporary directory for byte comparison. Use `--no-rebuild` only when
a fresh deterministic build is not desired. `--equations DIR` selects a
separate generated tree; `--receipt FILE` writes a verification receipt.

The delivered normal and optimized receipts are in `receipts/`. Both
full runs passed, including fresh byte-identical rebuilds of all 35
equation JSON files. The optimized run checks that acceptance does not
depend on Python `assert` statements that disappear under `-O`.

The supplementary shell and reciprocal arithmetic fixtures can be run by:

```sh
python3 code/check_shell_encoding.py
python3 code/check_reciprocal.py
```

To regenerate mathematical typesetting:

```sh
python3 code/render_release_tex.py
python3 code/check_tex_residuals.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses the conventional LaTeX packages named in its preamble.

## Layout and exact data convention

- `report.tex`, `report.pdf`: mathematical account, comparison, limitations,
  and all 386 literal residuals of the main equation.
- `tex/`: generated residual lists for all three equations and fingerprints.
- `equations/integer660/`: final integer residuals, expansion, raw ledger,
  domain certificate, guard system, elimination certificate, and metrics.
- `equations/natural363/`, `equations/natural364/`: complete natural forms
  with their contraction certificates and expansions.
- `equations/sources/`: generated source systems and their proof metadata.
- `code/`: portable generators, independent finite checkers, and renderer.
- `proofs/`, `reviews/`: new proofs and independent mathematical reviews.
- `receipts/`: completed normal/optimized verification and supplementary checks.
- `provenance/`: inherited inventory and comparison information.
- `upstream/ConZFC_407_888_Quartics/`: unchanged selected dependencies,
  original notices, proofs, and calibration excerpts.
- `SHA256SUMS`: fingerprints for the delivered files other than the manifest.

Residual and expanded polynomial terms have the form `[coefficient, indices]`.
The JSON indices start at zero. Thus `[7,[0,0,3]]` means `7*z_1²*z_4`,
and `[5,[]]` means the constant five. PDF indices start at one. The
`variables` list fixes the coordinate order; names are explanatory labels.
For an equation file, sum the squares of all listed residual polynomials.
For an expanded file, sum the listed monomials directly.

All natural-domain coordinates include zero. Dropping their domain
restriction would change those companion problems. Only `integer660`
is the delivered unrestricted-integer equation.

## Repository provenance and integration

Inspected repository: <https://github.com/VladimirReshetnikov/ProveIt>

Snapshot: `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`.
Immediate base: `docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip`.
Logical calibration pin: `08200eb10fde2db408c69dffd840d6920a569b1f`.

The selected inherited subtree contains 78 unchanged files, including all
51 files authenticated by its inherited source-pin manifest. The old
generated equations and reports are deliberately omitted. No changes
have been pushed to GitHub. The archive is ready to place in `docs/incoming`
or incorporate as a named contribution under the consistency project.
See `NOTICE.md` and the retained notices for attribution and scope.

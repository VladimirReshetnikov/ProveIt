# Build and verification instructions

All commands are run from the package root.

## Requirements

- Python 3.10 or later.
- `mpmath` for the optional high-precision diagnostics.
- TeX Live with `latexmk`, `pdflatex`, `lmodern`, `microtype`, `amsmath`, `mathtools`, `mathrsfs`, `cleveref`, `listings`, `fancyhdr`, and `lastpage`.
- `latexpand` to regenerate the standalone source.

No network connection is used by any replay or build step.

## Exact finite proof replay

```bash
python3 verification/generate_order10_certificate.py
python3 verification/verify_order10_certificate.py
python3 verification/verify_order10_certificate_independent.py
python3 verification/verify_normalization_spots.py
```

The primary replay constructs even Bernoulli residues from their defining recurrence and uses modular Gaussian elimination. The independent replay does not import the primary arithmetic module; it constructs all Bernoulli residues from the full recurrence and evaluates determinants by row-wise subset expansion.

## Exact explicit-identity replay

```bash
python3 verification/generate_explicit_identity.py
python3 verification/verify_explicit_identity.py
```

These commands reconstruct the displayed `(10,16)` identity by rational matrix inversion and exact centered asymptotics.

## Numerical diagnostics

```bash
python3 verification/numerical_check_explicit_identity.py
python3 verification/numerical_check_generators.py
```

The diagnostics are not proof gates. They are included to detect transcription, sign, anchoring, or branch errors.

## Complete replay

```bash
python3 verification/run_all.py | tee verification/VERIFICATION_LOG.txt
```

## PDF and standalone source

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexpand article.tex > article_singlefile.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error article_singlefile.tex
```

The modular article and standalone article should produce mathematically identical content. The distributed `article.pdf` is built from the modular source.

## Make targets

```bash
make verify      # full exact and numerical replay, with log
make pdf         # modular PDF
make singlefile  # expanded source and standalone compilation check
make all         # all of the above
make clean       # remove LaTeX intermediates and Python caches
```

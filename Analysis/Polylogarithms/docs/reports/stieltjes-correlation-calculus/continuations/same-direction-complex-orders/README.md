# Same-Direction Polylogarithm Products

Research continuation prepared for Vladimir Reshetnikov's ProveIt project,
October 10, 2026.

## Reading the package

`article.pdf` is the complete article; `article.tex` is its self-contained
LaTeX source, including the bibliography. The paper supplies full proofs,
not just experimental evaluations. The most direct reading route is:

- **Theorems 2.1–2.2:** the connected double-Hurwitz family is entire in both
  indices and retains its shift, stuffle, and finite harmonic interpolation laws.
- **Theorems 3.2 and 3.4:** the complex-order same-direction Mellin
  representation, including unequal positive scales and exact recovery of
  the existing positive-integer double-Hurwitz master.
- **Theorem 4.3:** an absolutely, locally normally convergent beta–Newton
  series, with independent spectral derivatives and harmonic-star coefficients.
- **Theorem 5.1:** a finite polynomial–Hurwitz algorithm for a nonpositive
  order and integral beta-kernel parameters, including filled resonances.
- **Theorems 6.1–6.2:** a coalescing Gamma-residue generator and an all-orders
  logarithmic moment formula with a proved depth drop from r+2 to at most r+1.
- **Theorems 7.1–7.2:** ordinary Stieltjes–Gamma kernel identities and fully
  anchored primitives at every index.

Section 8 separates the source comparison from safeguards against invalid
extrapolation. Section 10 gives ten further research questions. Classical
special cases are not presented as priority claims.

## What is resolved

The eighth research question in the inspected *Reciprocal Lerch Convolutions*
report asks for a same-direction spectral representation holomorphic in
both orders that recovers the finite double-Hurwitz master. The article gives
that representation. The positive-scale domain is explicit, and all real
integrals used as final identities are ordinary convergent integrals.

This is **not** a proof of generic finite closure at arbitrary complex orders,
a proof of arithmetic independence, or a proof of the Gaussian S6 or revised
S8 candidate. The existing positive-integer master is inherited and extended,
not counted again as a new solution.

Six archives in `docs/incoming` were listed but their compressed contents
were not inspected. See `SOURCE_AUDIT.md` for the exact provenance and audit
limits. No remote repository files were changed.

## Reproduction

Use Python 3.10 or later. Install the dependencies in `requirements.txt`
in a suitable environment; a different compatible version may work but was
not used for the delivered receipts. The last two dependencies are only
needed for optional PDF rendering.

```sh
python code/verify_exact.py
python code/verify_numeric.py --part all
python build.py
python code/inspect_pdf.py
```

The numerical suites can also be run individually:

```sh
python code/verify_numeric.py --part kernels
python code/verify_numeric.py --part moments
python code/verify_numeric.py --part spectral
python code/verify_numeric.py --part residues
```

The LaTeX build requires TeX Live or MiKTeX with the standard packages used
in `article.tex`. `build.py` runs three serial pdflatex passes without shell
escape, saves intermediate files under `build/`, checks reference convergence,
and copies the compiled PDF to `article.pdf`. `--engine lualatex` is available,
but the delivered PDF was built with pdflatex.

## Verification records

`results/exact_checks.json` records **824 passed exact assertions**, including
two deliberate corruption controls. `results/moment_reductions.json` contains
the generated multiple-zeta coefficient lists for logarithmic weights 0–8.

The four `results/numeric_*.json` files record **32 passed numerical diagnostics**.
They compare independent formulations, including a two-complex-order,
unequal-scale Barnes test, ordinary Stieltjes kernels, Gamma residues, and
logarithmic dilogarithm moments. Tolerances and observed relative errors are
stored per test. The spectral grid uses machine precision; its direct
comparison uses 23 decimal digits. Other numerical parts use 40 decimal digits.

**These diagnostics are not interval certificates.** Exact finite symbolic
assertions do not establish analytic convergence. Those proofs are in the
article. No Lean or other proof-assistant verification is supplied.

`results/pdf_review.json` records the delivered PDF's structural check and
rendered review. `code/inspect_pdf.py` regenerates page images and a contact
sheet for a fresh human review; a successful script run alone does not
certify that someone inspected the images.

## Integration

`integration/INTEGRATION.md` gives a proposed continuation path and precise
status-ledger wording. `integration/manuscript_insert.tex` is a compact,
prefix-labelled insertion with proof sketches and an explicit reference to
the standalone article for full proofs. The latter can be compiled for
syntax validation through `integration/check_insert.tex`.

Preserve the source audit and claim-status distinctions when integrating.
`SHA256SUMS` identifies delivered bytes. A rebuilt PDF may differ in metadata
and needs a new rendered review and checksum; the hashes do not certify mathematics.

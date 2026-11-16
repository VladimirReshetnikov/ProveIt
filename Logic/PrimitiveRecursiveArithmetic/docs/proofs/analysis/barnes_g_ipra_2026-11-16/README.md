# Barnes G-function in intuitionistic primitive recursive arithmetic

Prepared 16 November 2026.

## Main deliverable

- `paper/barnes_g_ipra.pdf` -- the 54-page human-readable research report.
- `paper/barnes_g_ipra.tex` and `paper/sections/*.tex` -- complete LaTeX source.
- `lean/` -- a self-contained finite-core scaffold, analytic certificate
  interfaces, and exact object-language targets for integration into ProveIt.
- `code/` -- exact-integer checks, rational product-tail certificates, high-precision regression checks, and a static scaffold audit.
- `evidence/` -- recorded output of those checks.
- `claims/coverage.csv` -- 38-entry source-by-source theorem ledger.
- `claims/source_audit.md` -- corrections and domain qualifications.
- `provenance/sources.json` -- inspected sources and pinned ProveIt commit.

## Scope and formal status

The report gives constructive, quantitative proofs for the canonical product,
functional equation, zeros, integer and finite-product identities, Taylor and
logarithmic-derivative series, integral and reflection formulas, multiplication
and duplication formulas, special values, Hurwitz-zeta and hyperfactorial
relations, the Barnes asymptotic expansion with explicit remainder contracts,
order two/infinite type, and constructive forms of the two uniqueness
characterizations.

The intended meaning of a real or complex analytic assertion in iPRA is a
*schema for each fixed primitive-recursive name and each requested precision*.
No sort of arbitrary real numbers or arbitrary functions is added to iPRA.
Compact domains, branch choices, denominator separation and error moduli are
part of the input certificates.

The finite integer core is checked by exact Python arithmetic.  The analytic
identities are supported by high-precision diagnostic checks and explicit
rational tail bounds.  The Lean files are a formalization scaffold, not a
completed kernel-checked analytic development.  No claim is made that the main
analytic theorem collection has already been compiled to
`LeanProofs.ConciseIPRA.Prf PRAAx`.


## Recorded validation

- 151 exact finite-arithmetic assertions passed for inputs through the recorded bound.
- 25 high-precision diagnostic records passed at 90 decimal digits; the largest recorded identity error is below `1.5e-89`.
- Three canonical-product tail examples lie below the proved rational majorant.
- The static audit found no proof-bypass token in Lean code, confirmed all advertised scaffold symbols, checked all 38 unique ledger IDs, and scanned all TeX sources for malformed fraction/control tokens.  This is not Lean kernel compilation.
- The PDF has 54 pages, opens successfully, uses embedded fonts, and was visually checked after rendering every page.

## Reproduction

```sh
./run_checks.sh
./build_pdf.sh
```

The PDF build uses ordinary `pdflatex`.  The numerical diagnostic requires
Python 3 and `mpmath`; the exact finite checker uses only the Python standard
library.

## Principal source corrections

1. The correct asymptotic characterization is
   `f(x+n) ~ Gamma(n)^x n^(x(x-1)/2) f(n)`, not `Gamma(x)^n`.
2. In the pure-imaginary modulus formula the prefactor is `|y|`, not `y`.
3. MathWorld equation (18) is an alternative form of its equation (17), not a
   third independent quarter value.
4. Complex logarithm formulas require a declared continuation path or a domain
   on which the chosen branch is separated from its cut.

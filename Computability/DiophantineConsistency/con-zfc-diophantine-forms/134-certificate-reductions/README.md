# Eliminating auxiliary witnesses in Diophantine consistency

Prepared for Vladimir Reshetnikov, 25 October 2026.

This research bundle supplies **four literal polynomial equations**, full new
ordinary mathematical arguments, a compiled paper with editable TeX, and offline
reconstruction and independent exact-algebra checks. Each equation's lack of
solutions, over its stated domain, is equivalent to `Con(ZFC)` by ordinary
mathematics formalizable in ZFC, composed with explicitly retained ProveIt
refutation calibrations. This does not prove either consistency or inconsistency.

Start with **[report/report.pdf](report/report.pdf)**. The new arithmetic proofs
occupy Sections 2–4; the appendices print all 386 quartic residuals and a complete
finite recipe for the compact equations' four fixed integers.

## Results

| Construction | Unknowns and domain | Degree | Quadratic residuals | Collected monomials | Coefficient height |
|---|---|---:|---:|---:|---:|
| New direct integer quartic | 314 unrestricted integers | 4 | 204 | 5,721 | 128,446 |
| Pinned package 131 parent | 324 unrestricted integers | 4 | 208 | 5,808 | 128,446 |
| New direct natural quartic | 233 nonnegative integers | 4 | 182 | 7,313 | 86,543,666 |
| Pinned package 129 recommended parent | 234 nonnegative integers | 4 | 183 | 9,019 | 87,741,134 |
| Pinned package 129 denser parent | 233 nonnegative integers | 4 | 182 | 50,762 | 88,674,690 |

| Compact construction | Unknowns and domain | Live binary operations | Exact degree |
|---|---|---:|---:|
| New `compact/equation78.json` | 10 strictly positive integers | 78 | 630 |
| New `compact/equation79.json` | 10 strictly positive integers | 79 | 468 |
| Pinned package 133 parent | 10 strictly positive integers | 84 | 436 |
| Pinned package 133 parent | 10 strictly positive integers | 85 | 328 |

The direct constructions strictly improve the displayed comparisons. The compact
constructions save six operations each while increasing degree. Their unchanged
four-coefficient tuple includes a 592,884-bit integer; that is the size of a fixed
port, not the height of the fully expanded polynomial. There is no claim of global
minimality, of a global variable-count record, or of literature-wide priority.

The comparison is against the immutable ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, including the actual artifacts in
packages 127–133. The collection overview was not yet current with all those
packages. The source ledger identifies exact inherited material.

## New mathematical mechanisms

1. **A polynomial Pell comparison center.** Given the existing auxiliary norm,
   `D = A + (1-A)*H^2` automatically supplies both comparison congruences. Its
   signed implementation, semantic anchor reuse, square cap, even frame, and odd
   auxiliary multiplier yield the 314-variable integer quartic. The full signed
   soundness and constructive completeness arguments appear in `direct/proof.md`.
2. **A descending-binomial factorial fixed point.** For `t >= 3`, `F >= 2`, and
   `F^2-1 >= t`, the identity
   `F = floor((F^2-1)^t / binom(F^2-1,t))` holds exactly when `F=t!`.
   The corresponding CRT moduli `F^2/i-1`, together with a one-row Pell cap and a
   horizon floor of 12, give the sparse 233-variable natural quartic. The entire
   new proof is in `report/natural_section.tex` and is included in the PDF.
3. **Staged denominator recovery.** A known large divisor first identifies a
   bounded Pell index. The exact index then recovers the full divisibility
   statement. This removes the compact branch's artificial scale `q^2+1`.
   `compact/PROOF.md` proves both existential directions, including fresh positive
   completeness witnesses and the exact global degrees.

The direct branches encode the numerical C222 proof calculus and use neither a
K215 simulation nor Jones's universal polynomial. The separate compact branch
retains its indexed native/K215 calibration. Classical Pell identities, the
original proof calculus, semantic-anchor and cap methods, compiler techniques,
and native coefficient construction remain credited to their inherited sources.

## What specifies the equations

- `direct/equation.json` is the entire 204-row residual list over 314 integers.
  The equation is the sum of all 204 residual squares, equal to zero.
- `natural/equation.json` is the entire 182-row residual list over 233
  nonnegative integers. Its equation is the sum of all 182 residual squares.
- Each adjacent `expanded_polynomial.json` gives every collected coefficient of
  the corresponding quartic, with no symbolic or unbounded placeholders.
- `compact/equation78.json` and `compact/equation79.json` give the complete finite
  arithmetic circuits. Every register is a polynomial abbreviation, not a new
  quantified variable. Literal coefficient bytes and their finite reconstruction
  are included in `compact/coefficients/` and `compact/rebuild_coefficients.py`.
- Generated `residuals.tex`, `residuals.txt`, and `variables.tsv` files make the
  direct equations readable. The printed TeX is parsed back into the exact sparse
  data during verification.

Sparse monomials are encoded as `[integer coefficient, [coordinate indices]]`.
Repeated indices mean repeated factors; an empty list is the constant monomial.
All coordinate indices start at zero. Factorials, floors, variable exponents,
binomial coefficients, and bounded-quantifier abbreviations occur in the proofs
only; none remains as a primitive in the final polynomial data.

## Reproduce offline

Python 3.10 or later, with its standard library, is sufficient. Run these commands
from the extracted bundle root:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
```

The runner resolves all paths relative to itself and also works from another
working directory. It reports the exact checks for all three components. The
optional rebuild uses temporary directories to reconstruct the direct outputs
and compares the selected mathematical artifacts byte for byte. The compact
circuits and all four coefficient numerals are reconstructed independently.

Use `--receipt /some/output/path.json` to save a replay receipt outside the sealed
bundle. Normal and optimized delivery receipts are in `verification/`.
The component READMEs describe their exact input boundaries. Reconstruction
requires no internet, external checkout, Lean installation, or machine simulation.

Compile the editable paper with pdfLaTeX twice from `report/`:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

A standard TeX Live installation providing the packages listed in the preamble
is sufficient. `report/report.pdf` is the supplied compiled version.

## Proof and verification boundary

The new lemmas and their composition are ordinary unbounded mathematical proofs.
The exact checkers authenticate the finite equations, expansions, substitutions,
restoration identities, numeral recipes, circuit topology, operation counts, and
leading forms. They include actual corruption controls, and run under `python -O`.
They do not infer universal nonvanishing from finitely many tested inputs.

The named C222/refutation and ZF/ZFC equivalences, and the compact native
calibration, are inherited. The relevant ordinary proofs, interface source files,
and exact source identities are included. The entire transitive Lean development
was not rebuilt, and this package does not claim a new end-to-end Lean/Rocq proof
or an encoded object-language ZFC derivation. Independent reviews in the bundle
were performed separately within this AI-assisted research workflow; they are
not outside human peer reviews.

## Repository integration

This is an intake-ready research bundle. No upstream files or branches were
changed. It can be placed as a new collection entry after repository review;
`INTEGRATION.md` provides a suggested summary and links without assuming a final
package number. Keep the domain, all measured costs, and the formalization boundary
with each endpoint. In particular, do not compare 233 natural variables directly
with 314 unrestricted integer variables as though their domains were identical.

`PROVENANCE.json`, the component source ledgers, inherited license notices, and
`SHA256SUMS` preserve the reproducible comparison boundary and file identities.
On systems providing `sha256sum`, run `sha256sum -c SHA256SUMS` from the bundle
root to check every delivered file against the sealed manifest.

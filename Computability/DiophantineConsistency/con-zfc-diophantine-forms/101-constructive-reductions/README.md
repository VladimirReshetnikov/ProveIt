# Smaller Diophantine equations for ZFC consistency

This packet supplies **seven explicit ordinary polynomials**, new ordinary mathematical reductions, exact finite certificates, and a compiled article. It is prepared for incorporation into Vladimir Reshetnikov's ProveIt repository.

**Primary unrestricted-integer proposal:** `integer14/crt14_degree540.json`, with 14 unknowns, exact degree 540, and 160 live binary operations. Its 147-operation companion has degree 568. A separate direct construction yields a fully expanded quartic in 977 unrestricted integers.

For each polynomial and the domain shown below, the new proofs compose with explicitly named, pinned ProveIt calibration theorems to give an ordinary argument formalizable in ZFC:

> The polynomial has no solution in its stated domain if and only if Con(ZFC).

No assumption that ZFC is consistent is used in the equivalence. This is not a proof of the absence of solutions, a global minimum, a claim of historical priority, or a newly compiled end-to-end Lean/Rocq theorem. The precise proof boundary is discussed in the article.

## Read the article

- `report/ConZFC_Constructive_Reductions.pdf`: compiled article with complete new arguments, explicit formulas, comparisons, and logical dependencies.
- `report/ConZFC_Constructive_Reductions.tex`: main LaTeX source; it includes the three component `report_section.tex` files.
- `INTEGRATION.md`: suggested repository integration and comparison conventions.
- `SCHEMAS.md`: literal polynomial and certificate formats.

## Final equations

| Literal file | Domain | Unknowns | Exact degree | Additional measure |
|---|---|---:|---:|---|
| `nine/equations/boundary_simple.json` | Strictly positive integers | 9 | 1,472,168 | 420 operations |
| `nine/equations/boundary_complete.json` | Strictly positive integers | 9 | 997,810 | 1,057 operations |
| `nine/equations/compact_simple.json` | Strictly positive integers | 9 | 1,626,248 | 428 operations |
| `integer14/crt14_degree540.json` | Unrestricted integers | 14 | 540 | 160 operations |
| `integer14/crt14_degree568.json` | Unrestricted integers | 14 | 568 | 147 operations |
| `direct/equations_v3/cap64/equation.json` | Nonnegative integers | 495 | 4 | 391 quadratic residuals; 15,377 expanded monomials |
| `direct/integer977/equation.json` | Unrestricted integers | 977 | 4 | 533 quadratic residuals; 24,632 expanded monomials |

Each direct equation is the sum of squares of the listed residuals. Its directory also contains the entire collected polynomial in `expanded_polynomial.json`. The coefficient heights are 83,867,632 for the natural equation and 83,869,250 for the integer equation. The latter has coefficient 23 on its first variable to the fourth power.

All circuit registers are polynomial abbreviations, not extra unknowns. All coefficient ports are bound to fixed, materialized integer values. No variable exponent, binomial, factorial, inequality, or universal quantifier remains in the final polynomial data.

## What changed

1. **Four-root separation.** Keeping the positivity guard's square root explicit leaves four Pell radicals. A strict size ordering under the weak scale removes the former amplifier; CRT restores the cubic scale afterward. Polynomial root centers then lower the degree to 540. The 568/147 companion improves the inspected 696/150 fourteen-integer predecessor in both degree and operations.
2. **Radix origin normalization.** Position zero is valid in the positive nine-variable ratio interface. Translating all source weights by minus one and all extraction targets by minus two preserves the source identities. Recalibrating the binary population threshold and sharing powers yields the three new nine-variable circuits.
3. **Projection and domain recovery.** A projected eight-column direct source feeds synchronized arithmetic certificates. Its equations already force most signs. The shared Pell frame recovers 29 more signs, so only 170 coordinates need explicit ternary nonnegativity guards. Twenty-eight integer contractions give the 977-variable quartic, compared with the synchronized parent's 2,088-variable integer lift.

These are improvements relative to the inspected snapshot, not global optimality results. The 420-operation original31 equation uses larger coefficients than the compact54 form: their four-port native tuples occupy 533,099 and 215,492 raw bytes, respectively. The fourteen-variable tuple uses 615,883 raw bytes in six ports. Operation counts treat fixed leaves as available and count live additions, subtractions and multiplications, including squares and multiplication by numerals; they are not bit-complexity estimates.

## Reproduce

Python 3.10 or later and its standard library suffice for the mathematical artifact checks. From this directory:

```sh
python3 verify_all.py --output verification/rechecked.json
python3 -O verify_all.py --output verification/rechecked_O.json
```

The driver checks the delivered artifacts before running producers, works in a temporary copy, and compares reconstructed final equation files and coefficient leaves byte for byte. It also reconstructs the domain certificate, checks source pins, and exercises deliberate corruption rejection. The stored root receipts are `verification/ROOT_NORMAL.json` and `verification/ROOT_OPTIMIZED.json`.

These checks certify finite algebra, arithmetic data and explicit transformations. They neither search for a ZFC refutation nor experimentally verify the unbounded consistency calibration. The ordinary proofs supply those implications. No new proof-assistant kernel build was performed.

To compile the article, install a standard TeX distribution with `latexmk`, AMS packages, Latin Modern, `microtype`, `xurl`, and `hyperref`, then run:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error ConZFC_Constructive_Reductions.tex
```

## Provenance and integrity

Comparison snapshot: `7e533c33819ee1f703b69f2778a767cdc069940d` of `VladimirReshetnikov/ProveIt`. The root `provenance/COMPARISON_SNAPSHOT.json` records the incoming archive inventory and SHA-256 digests. Immediate component pins and source notices are retained, including the older direct calibration revision `08200eb10fde2db408c69dffd840d6920a569b1f`.

The direct branch uses `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. It encodes derivations in the numerical calculus C222, without simulating K215 or invoking Jones's universal polynomial. The compact branches preserve their identified native/compiler and machine/refutation calibration dependencies.

`MANIFEST.sha256` lists the final packet's files, excluding the manifest itself. Component review notes record separate AI reviews, not external peer review. Original notices are preserved; new contributions are distributed under the included MIT No Attribution license.

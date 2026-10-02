# Computational review and reproducibility scope

Date: 1 October 2026.

## Result

The portable implementation passed the recorded exact-algebra, independent-recurrence, inverse-reversion, and pointwise-diagnostic checks. A separate code review found no mathematical implementation defect. Two minor input-validation gaps identified in review were corrected before packaging: optional inverse/precision arguments are validated only when their checks are requested, and the reference fixture must have exactly the advertised 2001 indexed rows.

The final replay source SHA-256 is `3299318789bee95c2556a193fb302377fbc303c216147b0b336631a48e2e4dd1`.

## Independently reviewed formulas

- The exact rational z-series starts with the correct T₀ and uses the correct summand ratio. Because the j-th summand begins at zʲ, terms through j=M suffice through degree M
- The normalization hᵣ = (2√κ)ʳcᵣ turns each forward coefficient into a polynomial in κ with rational coefficients. In a term indexed by m+k=r, the scalar factor is 4bₘ(−1)ᵏ2^(m−k)(m+2+k)!/((m+2−k)!k!) multiplying κᵐ
- The original-f computation uses the original generating-function denominator, rather than merely restating the transformed g recurrence
- The q-series constructions of D and partial-theta B use their distinct formulas. The P product and literal finite-product E expression reproduce the exact remainder independently of A
- The logarithmic and Lambert-centered inverse residual equations are correct. Their symbolic reversion checks the displayed coefficients and vanishing residual at the requested order
- The numerical decomposition computes the original A and the finite-product E independently. Its outcomes are properly described as floating-point diagnostics, not proof certificates

The independent review ran additional small-degree checks at q-degrees 0, 1, 2, 3, 8, 16; verified h₀ through h₄; and compared the first 14 area coefficients with the article. The final full replay uses the larger default bounds recorded below.

## Recorded default full run

See `receipts/receipt.json` and its hashed outputs:

- All 2001 exact integers a₀,...,a₂₀₀₀ match the archived coefficient data
- Original f generating function = g recurrence through q⁹⁶
- Partial-theta B = rational-summand D through q⁹⁶
- A = P B² + R through q⁹⁶ using the separately constructed finite-product E
- Rational local and forward expansions through degree 12
- Logarithmic and Lambert-centered inverse reversion through order 4
- Five exact-integer asymptotic comparisons, up to n=2000
- Six real/nonreal pointwise identity checks at 90-digit working precision

The standard-library core also passed with site packages disabled (`python -S`). A zero-order boundary run and a further exact forward degree-20 run passed.

## Operational checks

See `receipts/safety-checks.json`:

- `-O` and `-OO` rejected
- Existing replay destination refused and verified unchanged
- Truncated reference fixture rejected
- Existing TeX build destination refused
- Safe-extraction helper rejected traversal, absolute paths, and symbolic-link entries before creating the extraction destination

Both Python programs make no network or subprocess calls. The TeX build script uses installed command-line tools, attempts no downloads, builds in a fresh destination, and disables shell escape. Its independently rebuilt PDF text exactly matched the shipped reviewed PDF. See `receipts/portable-tex-build.json`; the final visual approval applies to the shipped PDF hash, not a claim that PDF byte serialization is identical across engines or dates.

The complete package manifest covers these sources, audits, article files, data, and receipts. A separately reported final-archive receipt records fresh safe extraction, manifest verification, and replay from the extracted immutable ZIP. That external receipt is deliberately outside the ZIP: inserting a receipt of the final ZIP into that ZIP would change the object being verified.

## Limitations

Finite coefficient and series checks establish agreement only through their stated truncation degrees. Floating-point diagnostics are not certified analytic tail bounds. The program does not verify the whole-circle estimates, coefficient-transfer proof, combinatorial generating-function premise, literature novelty, or an effective threshold for eventual theorems. Those are separate mathematical questions addressed in the article and source reviews at their stated scope. This review is not external peer review or a proof-assistant formalization.

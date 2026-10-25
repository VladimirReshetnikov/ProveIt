# Cofinal witnesses and centered carriers for Diophantine consistency

Research iteration 19, prepared for Vladimir Reshetnikov, 25 October 2026.

Start with **report/main.pdf**, with editable LaTeX sources beside it. This archive supplies literal integer polynomials, ordinary proofs, complete coefficient tuples, inverse maps, source provenance and reproducible checks. No repository was modified.

## Selected results

Every direct equation below is a quartic; domain is part of the theorem.

| Domain and profile | Variables | Residuals | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| Unrestricted integers, dimension | 246 | 178 | 12,541 | 12,227 |
| Unrestricted integers, sparse | 247 | 179 | 4,352 | 23,316 |
| Unrestricted integers, balanced | 247 | 179 | 4,432 | 17,235 |
| Unrestricted integers, lower height | 247 | 179 | 5,648 | 6,144 |
| Nonnegative integers, cofinal dimension | 219 | 171 | 8,267 | 130,686,428 |
| Nonnegative integers, cofinal sparse | 221 | 173 | 5,253 | 65,867,916 |
| Nonnegative integers, noncofinal | 221 | 172 | 5,586 | 65,892,620 |

The new 247-variable sparse and balanced equations improve the matched incoming 252-variable/182-row/5,340-term/height-128,446 source on all four varying metrics. The 246-variable point trades support for dimension. Natural219 improves dimension, rows and support against the incoming low-height221 source but increases height; the 221-variable noncofinal point improves support and height at unchanged dimension and rows.

Small-variable circuits:

| Domain | Variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Strictly positive integers | 10 | 382 | 79 |
| Strictly positive integers | 10 | 338 | 80 |
| Unrestricted integers | 14 | 88 | 110 |
| Unrestricted integers | 13 | 156 | 117 |

Positive controls 78/516 and 79/456 are dominated and explicitly labeled. Earlier lower-degree positive tradeoffs and the previous 14/86/112 integer point remain separate choices. The root improvements use a polynomial integer-coordinate shear; they are not identical-polynomial recompilations in the original coordinates.

## Main ideas

- Compose a common remainder certificate with an odd-square radix, then expose and eliminate affine coordinates. The exact source edit has a separate acyclic sign proof, not just a polynomial substitution claim.
- Use an even descending-factorial horizon t=2t0+4 and a cofinal beta base y=V−1. Evenness supplies the divisibility needed by beta CRT; bounds on every pending-state factor prove completeness. This is not a natural-coordinate bijection.
- In the low-Y ten-positive chart, recover the exponential projection before full denominator integrality. The recovered power-of-two base then supplies the missing denominator divisibility. A degree tie in cT−R is retained in the exact leading form.
- Center two-root and three-root carrier coordinates to shorten the arithmetic DAGs, with explicit inverse integer shears and signed/zero-radicand proofs.

The proof also supplies two carefully limited obstructions: no affine-polynomial multiplier combination of the final246 residuals yields an affine consequence, and no polynomial shear of the single root-carrier coordinate lowers the stated 88/156 degrees. Neither is a global-minimum theorem.

## Coherent alternate radix47 specialization

`positive/` keeps the full original radix67 coefficient tuple. `positive_radix47/` supplies the same four free-port circuits with the entire incoming complemented-label radix47 tuple. All four numerical ports change coherently; the specialized polynomials differ.

Raw coefficient storage is 207,214 bytes instead of 295,388, and the largest port is 415,904 bits instead of 592,884. The encoding improvement is credited to the incoming Common Remainders–Radix47 construction. This is not the repository's separate conditional three-anchor47 proposal and is not claimed to be its currently adopted page. The package includes a full ordinary bridge, exact reconstruction, all 51 native linear identities and actual controller checks. Port names or numerical boxes alone are not used to justify the specialization.

## Files and exact specification

- `quartic/ENDPOINTS.json` identifies the four integer residual systems, complete expansions and certificates. Optional horizon-4 companions have unchanged headline metrics and coefficient L1 smaller by 288; their separate proof includes a complete 144-case factorial certificate with a proved exhaustive bound.
- `natural/natural219`, `natural/sparse221` and `natural/balanced221` are the three final natural equations. Earlier projected systems are explicit controls and sources for the row-basis certificates.
- `positive/q1_bv.json` and `positive/q2_bv.json` are the useful ten-positive endpoints; `_v2` files are controls. The alternate folder has its own complete binding.
- `roots/integer13_degree156_ops117.json` and `roots/integer14_degree88_ops110.json` are complete DAGs. Their six-port tuple is different from the positive branch and must not be mixed with it.

A sparse term `[c,[i,j,...]]` denotes c times the product of coordinates with those zero-based indices; `[]` denotes the constant term. A residual list defines its single equation by summing all residual squares. DAGs contain only fixed integer constants, quantified variables, addition, subtraction and multiplication. No variable exponent, factorial, floor, binomial or undecided predicate remains in a final equation.

The comparison snapshot is ProveIt `3ecd6a6cf53d47519228328567f45fb7ee9781d9`. `reviews/baseline.md` distinguishes incoming, placed and accepted sources and records exact hashes and complete metric comparisons. Source licenses and ordinary calibration dependencies are retained.

## Reproduce offline

Python 3.10 or later and its standard library suffice:

    python3 -B verify.py

This authenticates the full sealed inventory and runs all components in fresh disposable copies, separately in normal and optimized Python. It checks exact reconstructions, complete coefficient lists, every graph and leading form, literal source maps, corruption controls and unchanged sealed bytes. The original extraction is not modified.

Options:

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized --receipt /tmp/replay.json

Rebuild the report with a standard TeX Live installation:

    sh build_report.sh

Use a fresh extraction for a strict inventory replay after generating TeX auxiliary files. Standalone subsection QA PDFs and PNGs were omitted from this delivery; the final integrated PDF and review receipts are supplied. The root component's local inventory is restricted accordingly.

## Mathematical boundary

The ordinary proofs, composed with explicitly named inherited arithmetic and refutation calibrations, establish in ZFC that unsolvability in each stated domain is equivalent to Con(ZFC). This does not prove consistency or unsolvability. The direct branches use the numerical C222 calculus, not K215 simulation or Jones universality; the small-variable branches retain their stated native ancestry.

Finite replay is not used in place of an unbounded proof. No fresh end-to-end Lean/Rocq certificate, encoded object-ZFC derivation, literature-wide priority or globally simplest equation is claimed. Independent reviews are separate AI-assisted mathematical/artifact checks, not outside human endorsement.

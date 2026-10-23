# ProveIt integration notes

Reviewed upstream revision: 124c07c0b77a9e20e84676514d8b1ff78536ea3f.

## Suggested placement

The package is self-contained. A possible next numbered directory is:

    Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-support-majorants/

The repository maintainer should choose the actual number to avoid collision
with concurrent incoming work. Alternatively, place the delivered ZIP in
docs/incoming for the established intake process. No repository content was
changed or pushed as part of this research delivery.

## Suggested catalogue entry

Smaller support-aware and overlapping quadratic sources; a polynomial
radical majorant and existing-witness separator for the nine-variable tail.

Principal points:

- 9 positive integers: degree 15,534,796; 655 binary arithmetic operations.
- 9 nonnegative integers: degree 15,534,796; 658 operations.
- 10 unrestricted integers: degree 39,914,856; 651 operations.

Additional operation-count tradeoffs are in README.md and report.pdf.

The new source specializes the 31-positive-variable, 22-quadratic parent.
It protects 71 present monomials against all 528 pairs with width 179 and
overlaps row bands with final target 5775. The principal nine-variable
finalizer uses scale 2048, a strict polynomial radical majorant, and the
existing h coordinate. These are local mathematical reductions with
explicit finite certificates.

## Review entry points

1. report.pdf, Sections 3–5: all new source and finalizer proofs.
2. report.pdf, Appendix B: exact-degree proof and the D^16 certificate relation.
3. proofs/FOUNDATION_AUDIT.md: inherited compiler/calibration dependencies.
4. verify_release.py: one-command finite audit.
5. refined/overlap_nine_positive_major2048.json and
   generated/overlap_ten_integer.json: primary equations.

The four native ports are the coherent package 31 tuple. Preserve
data/ports, data/coefficient_recipes.json, and their provenance together.
The complete fixed leaves are additionally materialized under data/fixed.

## Labels that preserve the proof boundary

Use "explicit ordinary mathematical equivalence, with independently checked
finite algebraic certificates." The source and tail reductions are proved
in the manuscript; the compiler and machine calibration are identified
inherited theorems. Do not label this as a newly completed end-to-end Lean
proof or a numeral-coefficient object-language ZFC certificate.

The low-variable degree improvements do not supersede the P67 point on
operation count alone. No global optimality or new variable-count bound
is asserted.

## Files to retain

Retain the six top-level TeX source files, report.pdf, code, data, generated,
refined, proofs, provenance, inherited notices, and verification receipts.
SHA256SUMS is an immutable release inventory; after intentional edits,
regenerate it when preparing a new version. RELEASE_VERIFICATION.json is a
mutable run receipt and is deliberately excluded from that inventory.


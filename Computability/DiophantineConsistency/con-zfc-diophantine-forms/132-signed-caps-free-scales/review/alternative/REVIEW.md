# Independent literal review of the 355- and 352-variable signed-cap artifacts

25 October 2026. Both variants pass independent finite replay in normal and optimized Python modes. The receipts are identical. No producer module is imported or executed by this checker.

## Results

- Positive auxiliary variant: 355 unrestricted integer variables, 220 quadratic residuals, degree 4, 9,370 collected monomials.
- Odd auxiliary variant: 352 unrestricted integer variables, 219 quadratic residuals, degree 4, 9,355 collected monomials.
- Both collected polynomials have coefficient height 15,020,718 and residual coefficient height 2,203.
- Both replay all 229 integral monic restorations and identify exactly 141 unused coordinates. Every retained coordinate is live in the output residuals.

## Exact finite checks

The parent is pinned to the prior independently reviewed squared-paired source. Its complete JSON is also compared with that preceding source. The fresh cap checker derives all sixteen seed exponents from the original index rows, derives the permitted deletion set from those row families and guards, and demands exactly 85 deleted and 434 retained parent rows. Every retained row and declaration is unchanged. It independently constructs every new cap variable, product gate, norm, progression, aggregate, pooled residue, and three-square guard, and compares the complete raw object. The odd variant permits exactly the aggregate slack guard, with no auxiliary-quotient guard.

The inherited independent polynomial replay kernel verifies all 17 original square roots, all 11 Horn product links, all 18 exact rewrites, both deleted bundle rows, and the protected-coordinate no-escape boundaries. It reconstructs and compares the entire factored source. It then verifies each monic restoration against the actual current row, checks acyclic live dependencies and degree, performs every substitution, and compares the final partition, remapping, declarations, and residuals. Finally it expands the sum of squares over the integer polynomial ring and compares every collected coefficient. Deterministic evaluations are supplementary only.

Each variant also rejects 19 deliberately corrupted artifacts. Controls target retained and deleted inventories, cap index and seed labels, cap norms and both auxiliary-factor forms, the aggregate and pooled residue, extra guards, square roots, Horn links, rewrite ledgers, protected-coordinate escape, factor endpoints, restoration arithmetic and cycles, output partitions, and a final expanded coefficient. Selected factor mutations refresh the affected hashes so rejection reaches the substantive replay; projection certificate aliases are synchronized for the restoration controls.

## Independence and scope

The polynomial arithmetic and Horn/projection replay were copied from the independently reviewed wave15 checker. The cap-source inventory and formula checker is new. Only the Python standard library is imported. No producer PASS result is used as evidence. PROVENANCE.json records the reused independent checker and the exact parent binding.

This is a finite literal source-to-polynomial audit. The unbounded signed-cap theorem, the even-index odd-quotient completeness argument, and the incoming ordinary arithmetic/C222/ZFC calibration are mathematical dependencies, not conclusions from finite tests. They are discussed in the accompanying proof and signed-cap review. No new formal proof-assistant certification is claimed.

## Reproduction

python -B audit_cap_independent.py --package /path/to/alternative --output /path/to/review

python -B -O audit_cap_independent.py --package /path/to/alternative --output /path/to/review/optimized

The complete receipt is INDEPENDENT_CAP_REPLAY.json; optimized/INDEPENDENT_CAP_REPLAY.json is the second-mode receipt.

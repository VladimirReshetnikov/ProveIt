# Review of the new Con(ZFC) Diophantine packages

## Provenance and verification

Current immutable pin: `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.
Previous review pin: `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms

The new wave removes packages 01–08 from the current tree and replaces them with 09–15. Those older packages remain available at the previous pin. Package 15 is our previous round-two release, not an independently new mathematical construction; its `final_forms.json` is byte-identical to the local previous release.

`SOURCE_PINS.json` records 127 fetched source files, their immutable URLs, Git blob SHAs, SHA-256 hashes and byte counts. All 127 exactly reproduce their verified Git blob after removing a transport-added terminal newline where necessary. Each package's `TREE.json` records its recursive source tree at the new pin. Reports, proofs, circuits and recipe specifications were read as inert data. No received repository code was run, no software was installed, and no public repository was changed.

The newly authored `independent_gate_audit.py` checks 62 explicit arithmetic circuits: operation counts, live gates and inputs, syntactic degree bounds, and modular univariate degree diagnostics. All 62 pass the stated operation/liveness/degree diagnostics. The modular diagnostic does not substitute the enormous actual coefficient tuple and is not a proof of fixed-coefficient degree or compiler soundness. Uniform leading-form and positivity proofs remain necessary.

## Actual progress beyond the previous delivered report

1. Package 09 merges the first and auxiliary square roots to reach 14 positive unknowns at degree 121 / 76 operations, much lower degree than the prior 14-variable degree-293 construction. It then merges all three roots with a weighted primitive element, reaching 13 positive unknowns at degree 571 / 84 operations or degree 515 / 85 operations. Its explicit strict denominator proof is essential; the initially unweighted resultant is not a sound replacement by itself.
2. Package 10 groups unit equations before taking sums of squares. Its four residuals give degree 56 in 15 positive unknowns at 74 operations, versus the earlier 78. Grouping depends on the first and main norms excluding the negative unit.
3. Package 11 gives a head-filtered four-cell T compiler with 37,075 tiles and B=2^(5^18), versus the previous report's head-restricted nine-cell B=2^(5^43). Initialization is recognized on the outgoing temporal edge; globally impossible local tiles are safely forbidden, and extra head-free margins justify the head filter under helical seams. Coefficient improvement is separate from arithmetic-operation improvement.
4. Package 12 shifts the positive transport quotient, saving one operation for systems and direct sums of squares, though not automatically for unit products. Its auxiliary gap produces degree 22 systems and degree 44 SOS with fewer operations than package 15. Applying that gap before root elimination gives a 14-variable degree-219 polynomial at 75 operations.
5. Package 14 extends the signed domain to require only seven positive coordinates, using an odd auxiliary multiplier and a square power scale. This gives 29 unrestricted integers. Oddness and squareness are existence-preserving canonical witness choices, not statements true of all old witnesses. The zero square-scale branch is excluded by reducing the main norm modulo H. The signed-main-root argument is separately proved.
6. Packages 09 and 12 independently reduce the positive quadratic lift to 32 variables / 23 equations, hence a quartic polynomial in 32 variables. The different R-elimination presentations use the same unknown count.

## Positive single-polynomial frontier at this pin

This is the known delivered frontier in (unknown count, exact degree, charged arithmetic operations), not a global minimum. Coefficient height is a separate criterion. Repeated identical rows are listed once.

| Positive unknowns | Degree | Operations | Source |
|---:|---:|---:|---|
| 13 | 571 | 84 | 09 weighted-root product |
| 13 | 515 | 85 | 09 lower-weight product |
| 14 | 342 | 73 | 09/10/12 outer root elimination |
| 14 | 219 | 75 | 12 gap norm |
| 14 | 121 | 76 | 09 two-root amalgamation |
| 15 | 155 | 67 | inherited 06/08; rebound to T4 in 11 |
| 15 | 123 | 68 | inherited 06 |
| 15 | 99 | 69 | ordinary-strong product, several packages |
| 15 | 93 | 70 | 12 auxiliary-gap product |
| 15 | 83 | 71 | 15 double-gap product |
| 15 | 56 | 74 | 10 grouped SOS |
| 15 | 44 | 78 | 12 auxiliary-gap SOS |

For low-degree lifts with no directly comparable charged-operation count: 20 variables at degree 8 and 25 at degree 6 remain package 15's results; the quartic improves to 32 variables in packages 09 and 12. Degree-293 / 75-operation root elimination is now dominated by the degree-219 gap norm at the same number of variables and operations. The 14-variable degree-144 / 81-operation SOS is dominated by the degree-121 / 76-operation product.

There is still no delivered polynomial below 67 operations. The smallest delivered systems cost 60 operations: 15 variables / 6 equations / degree 28 (12), or 16 variables / 7 equations / degree 24 (09). The lowest-degree 15-variable system is degree 22 at 61 operations (12). The 13-variable systems have 4 equations, degree 544 at 78 operations or 488 at 79.

Over unrestricted integers, 29 variables is the delivered minimum in this family. Package 14 gives degree 300 / 119 operations, degree 236 / 120, degree 188 / 121, and a degree-100 SOS at 130. Package 12's 33-variable degree-88 SOS remains a degree tradeoff. The earlier 31-variable degree-188 / 127-operation result is dominated numerically by 29 / 188 / 121, although its primary T4 coefficient binding is smaller.

## Cautions and discrepancies

- All seven replay drivers depend on omitted vendored files or ignored ledgers in the placed repository tree. The current README explicitly discloses this. Do not claim those drivers were successfully run in place, and do not treat missing files as missing mathematical theorems: `PLACEMENT.md` maps their archived sources.
- Package 15's final CSV omits a 14-variable SOS present in its report. That omitted row is not frontier-changing.
- Package 11's comparison notes retain older recommendations about the 34-variable lift and do not reflect its final T4 recipe throughout. Use its final `INSTANCE.json` and T4 bridge specification, not an earlier comparison paragraph.
- Identical local tile counts do not imply identical coefficients. In particular, 09 and 13 have different forbidden selector-1 tiles. Only whole four-tuples may transfer, after checking the compiler interface; never splice coefficient ports.
- Package 12's 60-operation shifted-quotient system does not by itself imply a 66-operation product. The equation compares a residual to zero; a product finalizer must restore the corresponding unit factor and pay its arithmetic cost.
- The extra denominator and signed-quotient arguments in 09 are not cosmetic. Root elimination initially recovers signed f, tau and y, and it must not invoke a theorem requiring positive T before sign recovery.
- No package formalizes the full Diophantine bridge in Lean/Rocq or proves Con(ZFC). The endpoint evidence concerns the underlying machine calibration; the new reductions are ordinary mathematics internalizable in ZFC. Two-sided independence should not be claimed from consistency alone.
- Coefficients are exact finite recipes, not materialized numerals. Even T4's B−1 has approximately 477 GB of binary digits.

## Highest-value combinations to investigate

1. Combine 09's weighted three-root merger with 14's seven-positive domain and canonical parity. Canonically c,R,f,i,tau,y are odd, V odd forces T odd, and M=f²+(cT)² is even. Hence merged t=M*tau+y is odd and can be encoded as 2r+1 instead of by a three-variable positivity map. This suggests 27 unrestricted integers. Soundness still needs the weighted denominator estimate with h merely nonnegative and signed T, and the signed-main-root recovery. This is a research lead, not yet a verified construction.
2. Combine 10's grouped unit equations with 12's gap residual. Grouping main norm and transport keeps degree at most 22, so a degree-44 SOS may use fewer than 78 operations. Grouping both pairs as in 10 trades degree 44 for degree 50. Count the shifted quotient carefully.
3. Search weighted-root formulas and evaluator reuse rather than merely lowering a nominal weight. The 13-variable resultant's high degree is now controlled either by the weighted A term or the e term; changing weights alone stops helping once e dominates.
4. Further head-sensitive T pruning and tighter bands can reduce coefficient height without changing the arithmetic. Preserve helical-seam completeness and the marked periodic-plane soundness argument; arbitrary local pruning is not sufficient.
5. Reducing another quadratic lift register, or moving between the quartic/sextic/octic presentations, is a separate variable-degree tradeoff from the minimum-operation goal.

These targets were communicated promptly for parallel mathematical investigation. This review does not count an unverified proposed combination as a new record.

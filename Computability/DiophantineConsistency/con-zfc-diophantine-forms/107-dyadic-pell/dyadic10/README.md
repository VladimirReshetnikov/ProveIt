# Dyadic separation and three centers: a degree-706 Con(ZFC) equation

This component defines one explicit integer polynomial N in **ten strictly positive unknowns**. Relative to the pinned native compiler/calibration theorem, ordinary mathematics formalizable in ZFC proves

    (N has no positive integer zero) <=> Con(ZFC).

Its exact total degree is **706**, and its literal circuit has **133 binary operations**: 79 multiplications, 33 additions, 21 subtractions. All fixed coefficient payloads are included and authenticated by SHA-256. They are coefficients, not additional variables. The polynomial can also be read over ten nonnegative integers by replacing each unknown x with x+1; its degree stays706 and this adds at most ten additions.

The immediate parent at the pinned ProveIt commit has ten positive unknowns, degree 816 and 124 operations. The new polynomial lowers degree by 110 (13.48%) at the cost of 9 operations. This is a tradeoff. It is not a minimum-variable record, does not establish global minimality, and does not avoid the inherited K215/native compiler calibration.

## Changes that matter

- Make both scaled Pell parameters use lambda=2(q^2+1), so the four rational radicands have odd numerators and odd denominators for every positive input.
- Give the roots, in the order auxiliary/strong/first/main, weights 1,2,4,8. A common irrational square class cannot cancel, by the unique smallest 2-adic valuation of its weighted rational ratios.
- This replaces the size-order argument and permits the strong ordinate I=ic^2, removing its old factor q^2+1.
- Center the carrier at the three leading root terms V+2AI+4V0k.
- Use the quadratic transport majorant L=(k+F+1)(T+alpha+6). An explicit lower bound on the canonical auxiliary gap proves the centered sum variable stays positive.
- Distribute W=1+(q-1)L into the carrier, saving one operation without changing the polynomial.

The proof handles all positive inputs, including those where the auxiliary register V is initially negative. It cancels the new factor 8 in the main projection using the odd modulus H, and separately proves the exact degree with formal Laurent series. No numerical inference replaces these steps.

## Files and replay

- `PROOF.md`: exact polynomial recipe, new arguments, inherited interfaces, exact-degree proof and limits.
- `INDEPENDENT_REVIEW.md`: independent review of the new semantic arguments; its scope is stated explicitly.
- `circuit.py`: literal division-free circuit and evaluator.
- `build.py`: coefficient authentication, topology/liveness checking and deterministic JSON generation.
- `p10_dyadic_degree 706.json`: emitted polynomial circuit and coefficient ledger.
- `audit.py`, `CHECKS.json`: independent formula checks, complete modular line-degree checks, parity/majorant cases and canonical-gap cases.
- `coefficients/`: the four complete compressed integer payloads.
- `upstream/PROOF816.md`: unchanged immediate-parent proof for the inherited Pell statements and reconstruction.
- `SOURCE_PINS.json`, `NOTICE.md`, `LICENSE`: provenance and attribution.

Run, using Python 3 and only its standard library:

```bash
python3 -I build.py --check
python3 -I audit.py
```

The finite checks support the proof. They do not search for a target zero, decide the equation, prove Con(ZFC), or certify the upstream compiler end to end.

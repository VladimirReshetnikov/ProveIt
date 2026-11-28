# Initial-average regression: scope and results

Run `python3 check_initial_average.py > initial_average_results.json`. The program uses only the Python standard library and exact integer arithmetic.

The finite model has two edges in each half. Its false ranks are (1,1,2), its true ranks (2,2,3), so the final inclusions are rectangular. The full grid ring is Z/(4q), the false observation ring Z/(2q), and the true observation ring Z/4, for q=1,3,5,7,11. Both terminal gauges are fixed at the identity; the true initial gauge is diag(g_false,0,1). The reduced gauge group is GL_1(Z/(4q))^2 × GL_2(Z/4), after removing the already identified unused true initial slot.

Every element of the reduced gauge group is enumerated. The script computes its inverse action on the standard inclusion tuple, groups equal observations, and verifies that every transporter fibre has exactly two elements. It separately evaluates the original transformed-inclusion predicate on selected whole transporters. It identifies the stabilizer exactly as g_false,0=1, g_true,1=1 and g_false,1 in the kernel of reduction to Z/(2q). The joint reduction to Z/(2q)×Z/4 is checked injective.

Two nontrivial sign characters are used. One is trivial on the stabilizer, and its normalized orbit values attain both +1 and −1. The other is nontrivial on the stabilizer, and every orbit sum is exactly zero. The latter checks the cancellation branch of the universal character-sum argument, without assuming that characters descend through the false congruence kernels.

Two off-orbit examples per ring are checked directly. One has a rank defect. The other has every edge split-injective but violates the common-initial-node compatibility; this shows that the orbit test is not merely checking individual injectivity.

Observed successful totals:

* 60,288 gauge elements enumerated;
* 30,144 complete orbit fibres checked;
* 422,016 direct transporter-predicate checks;
* 9,216 determinant-character multiplicativity checks on GL_2(Z/4);
* 10 off-orbit examples.

Across all five choices of the twist factor q, the core normalizing integer is 2. The original unused true initial coset has cardinality 96, so the original average's normalizing integer is 192. Both are independent of q, as the CRT proof predicts. After normalizing, the coefficient budget is 1.

These rank sequences are a small model of the general anchored-chain theorem; they are not an admissible parameter instance of the source's GRH construction. The program is finite algebraic regression, not a universal proof, a Lean compilation, or verification of any theta identity. The universal proof and source integration are in `initial_average_collapse.md`.

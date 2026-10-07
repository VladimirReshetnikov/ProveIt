# Validation and limitations

## Executed checks

Command:

```sh
python3 code/run_checks.py
```

The delivered run completed successfully, with:

- 9,999 root-grid inequalities, one for each integer order from 2 to 10,000;
- 40 exact character-distribution checks;
- 1,304 exhaustive forbidden-set/order partition cases;
- 1,826 exhaustive full-domain maps, tested at three orders (5,478 cases);
- 256 conservative BSG cores and their largest-cell size/energy checks;
- 100 sampled partial maps in mixed-torsion groups;
- 200 Gaussian-integer weighted exactness and energy-retention cases;
- five primary-torsion obstruction families, including exhaustive two-point
  checks for the indicated finite instances;
- exact integer verification of every rounded order-eight exponent.

The detailed machine-readable output is `checks/results.json`. The sampling
seed is 20261006. Elapsed time is informational and varies by environment.
The run log is included. No test failure was suppressed.

All group, character, rational-threshold, counting, and Gaussian-integer
arithmetic is exact. The scripts are not a proof assistant and finite testing
does not establish the theorems for all groups.

## Mathematical proof checklist

1. The character small-ball test is strict. A closed ball at radius 1/5 would
   fail the one-half estimate on fifth roots of unity.
2. Nonzero order-two and order-six elements are explicitly included in the
   root-grid argument, where the surviving fraction can equal one half.
3. Greedy separation needs no independence between defects.
4. Half-open cells force the difference of two m-term sums strictly inside the
   radius-1/5 ball.
5. Distinct vertical translates of a graph are disjoint. This removes the
   original-domain-size factor from the defect budget.
6. The Plünnecke–Ruzsa argument is given with a minimizing subset and the
   triangle injection, rather than treated as an unexplained exponent rule.
7. The BSG proof counts ordered bad pairs and permits repeated vertices in
   its four-edge walks. The label injection and difference recovery are stated.
8. The selected-core size M and original size n are kept distinct. The selected
   difference ratio is `2^24 alpha^(-10)`, not `2^21 alpha^(-9)`.
9. The same largest cell meets both final size and energy conclusions through
   `|mB'| ≤ K^m M`; unrelated favorable-cell choices are not conflated.
10. Exact Freiman relations permit repetitions. This is also essential for the
    lower-bound examples and for order padding.
11. The exponent theorem concerns the defect-coloring invariant. It does not
    establish optimality of the graph extraction exponent.
12. The original Lemma 9.3 statement already has a corresponding theorem in the
    pinned repository. The present paper does not claim a new formal closure.

These are internal mathematical consistency checks, not independent peer
review or a second proof-assistant certificate.

## PDF build

The article was compiled with pdfLaTeX through latexmk. The final PDF contains
23 pages. Cross-references and citations resolved, with no overfull-box or
undefined-reference warnings in the final build log. The PDF was rendered with
Poppler and visually inspected, including the title page, contents, theorem
and constant pages, tables, and references. Source and PDF are supplied together.

## Claims not certified by this package

- Human peer review or independent referee approval.
- Lean/Mathlib verification or a successful build of the repository.
- Exhaustive publication-priority assessment.
- An improved global bound for Szemerédi's theorem.
- Preservation of an entire derivative spectrum or compatible cross-sections.
- A polynomial-time algorithm on compressed group descriptions.
- Optimality of the numerical order-eight constants.

# Beyond Dirichlet GRH

Open **report.pdf** for the complete paper. Its source is **report.tex** and the six TeX sections beside it. All verification programs use Python's standard library.

## Results

- For finite products of local rings with square-zero maximal ideal, the proof classifies when upper density can stay positive as factors are added. It determines the leading density loss at fixed residue field, in both parities, also for bounded unequal exponent gaps.
- For rank-two integral graph towers, the report gives an explicit height bound on the start of spanning-tree stabilization. It determines the threshold in the loop count for linear worst-case growth in voltage bit length.
- For complete bipartite edge polytopes, the proof gives simple canonical-line zeros through smaller part 33 and two interlacing families through base width 32. The other part is unbounded. Exact finite polynomial identities establish that uniformity.
- For Lubin–Tate branch interpolation, the report characterizes equality in the previous pole-order bound and gives exact formulas at contact height one or precision two.

The source manifest identifies the upstream files and records the predecessor archives. The PDF gives the relation of the results to the earlier work.

## Reproduce

From this directory, with a usual LaTeX installation including Latin Modern, run pdflatex on report.tex twice. Cross-references settle on the second pass.

Run the following commands with Python 3.9 or later. Keep assertions enabled. The largest-width Bezoutian certificates use exact integer determinants and are appreciably slower than the example checks.

    cd checks
    python3 check_local_rings.py
    python3 check_sharp.py
    python3 check_onset.py
    python3 verify_ehrhart.py 2 32
    python3 verify_interlacing.py 2 32
    python3 verify_smaller_part.py 2 32
    python3 check_instances.py
    python3 check_branch_precision.py

The Ehrhart checker verifies polynomial degree bounds, positivity of Bezoutian minors, and the square boundary case. The two interlacing checkers use exact Sturm sequences and Newton differences for the two part-size directions. The smaller-part checker includes the transition to width 33. The accompanying text files record the calculations. Run times vary by machine.

The finite-ring, graph and interpolation programs corroborate examples and intermediate calculations in the general proofs. The Ehrhart positivity checkers supply the finite computations invoked by the proof itself. The upstream Lean validators were not run in this study. The new results have written mathematical proofs and Python checks.

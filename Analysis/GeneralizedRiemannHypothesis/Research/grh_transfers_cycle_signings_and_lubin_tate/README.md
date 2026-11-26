# Optimal signings of square cycles and sharp Lubin–Tate jet recovery

Open **report.pdf** for the complete mathematical report. The source entry point is **report.tex**, which includes **lubin_tate.tex** and **first_depth.tex**. All files may stay in the same directory.

## Results

- For the square of a cycle of length 8m with m at least 4, the report determines the exact minimum spectral radius over independent signs on every edge, all minimizing switching classes, the second distinct radius and a positive gap to the remaining classes. It determines the first even length at which the alternating optimum fails. A corollary maximizes the angular separation of nontrivial signed Ihara poles from the real axis.
- The local interpolation theorem gives the least precision, separately on every reduced Lubin–Tate branch, that determines a bivariate jet. It treats optimal direction sets and coefficient rings modulo powers of the uniformizer.
- For Berger and Sprang's invariant s₀(n) over the unramified quadratic field, the report gives an exact first-depth criterion for small digit sums and proves that s₀(n) − n is unbounded for each fixed prime p.

## Reproduce the finite evidence

Run the commands below in this directory using ordinary Python 3.9 or later with assertions enabled. All five verifiers use only its standard library. Each paired text file records the output in the delivered run.

| Command | Check | Output |
| --- | --- | --- |
| `python3 verify_graph.py` | Rational boundary recurrence, independent dense integer determinants, symbolic Floquet determinant and cutoff inequalities | graph_certificate.txt |
| `python3 verify_by_permutations.py` | Signed-permutation determinant sums, cyclic pruning and the stronger 43-sign window | permutation_certificate.txt |
| `python3 verify_small_cycles.py` | Exact finite classification for 8, 10, 12 and 14 vertices, including both signs around the cycle | small_cycle_certificate.txt |
| `python3 check_lubin_tate.py` | Branch precision, balanced choices and explicit integral witnesses in the tested cases | jet_checks.txt |
| `python3 check_first_depth.py` | Actual rational coefficients of the Lubin–Tate exponential on trace-kernel generators, and later logarithm rows | depth_checks.txt |

The graph calculations establish finite lemmas used in the proofs. The two arithmetic scripts cross-check examples of the algebraic theorems. Decimal display values and the figures take no part in any certificate.

## Rebuild the paper

Run `pdflatex report.tex` twice in a LaTeX installation with amsmath, amssymb, amsthm, graphicx, array, booktabs, microtype, geometry, xcolor, fancyhdr and hyperref. The vector figures are included. Running `python3 plot_optima.py` regenerates both figures and requires Matplotlib.

## Sources and verification status

The research note links to individual Lean files at commit 72fead102f663d5c7a407964a13dc0cf9d977207, to the original articles, and to the earlier 32-vertex witness. The file incoming_inventory.tsv lists the 41 ProveIt archives at commit 48efe71a726dddc5a505534edaa4c0fd190416b9 and their Git blob hashes. Scoped comparison and mathematical dependencies are described in the paper. The upstream Lean verification is project-reported. This packet contains mathematical proofs and Python checks for its own results.

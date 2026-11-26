# Beyond Dirichlet GRH

Read **report.pdf** for the research article, including the arithmetic and combinatorial proofs. The main LaTeX source is **report.tex**, which includes the four other TeX files in this directory. To rebuild with a standard TeX Live installation, run `pdflatex report.tex` twice.

## Results

* For every symmetric group from S3 through S12, an exact positive character identity proves a quotient of Dedekind zeta functions holomorphic away from 1. It gives the optimal local positivity constant n−1 in the reflection question from the ProveIt collection.
* A family of Stickelberger witnesses in the Lean argument admits an explicit formula for its gcd. At modulus five and weight one the least genuine witness is 8400 and the gcd of all genuine positive witnesses is 1200.
* The lower logarithmic density of a negative error in Suzuki's unsmoothed prime-power sum exceeds 99.992057%. The rare positive sign has uniform lower logarithmic frequency greater than 10^(-937).
* Fourteen cases of the balanced-anticode conjecture in ranks four and five have exact maxima and equality classifications. A five-element B3 set needs an abelian group of order at least 64. The cyclic minimum is 65.

## Reproducing the checks

Run the commands below from the extracted top-level directory, with Python optimization disabled (the ordinary default). The versions used were Python 3.12, SymPy 1.14.0, NumPy 2.3.5, and python-flint 0.9.0. The reflection and lattice computations use Python's standard library. On a machine missing the three numerical packages, install them with `python -m pip install sympy==1.14.0 numpy==2.3.5 python-flint==0.9.0`.

```sh
python checks/reflection/check_reflection.py
python checks/cyclotomic.py
python checks/suzuki/check.py
python checks/lattice/anticodes.py 4 2 3 4 5 6 7 8 9 10
python checks/lattice/anticodes.py 5 2 3 4 5 6
python checks/lattice/sidon.py
```

The accompanying TXT and JSON files give the expected results. The subgroup generator lists and rational coefficients are in `checks/reflection/certificates.json`. The checker derives each row from its generators and checks the full identity, including class sizes and the equality witness. The cyclotomic script works in rational polynomial rings and also searches for finite families attaining the stated gcds. For the prime race, `zero_cells.txt` contains the integer left endpoints of successive enclosing intervals in units of 10^(-22). The checker needs a few hundred MB of memory to sort the pair sums and differences. It relies on the published first-500 relation bound and the cited infinite-tail estimates. To regenerate the zero enclosures independently, run the following and then rerun the Suzuki checker.

```sh
python checks/suzuki/generate.py
python checks/suzuki/check.py
```

The group and lattice certificates and the new moment inequalities were checked as described in the article. The upstream Lean compilation and checker runs are those reported in the project's readable-edition README. The new results are paper proofs with exact or interval-arithmetic checks. The code here does not claim a Lean formalization of those results.

## Source snapshots

* [grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207) at `72fead102f663d5c7a407964a13dc0cf9d977207`. The article links to the relevant declarations in the readable edition.
* [ProveIt incoming reports](https://github.com/VladimirReshetnikov/ProveIt/tree/5cc267af75a635199ac5d93a7d49cbce521daefc/docs/incoming) at `5cc267af75a635199ac5d93a7d49cbce521daefc`. The CSV inventory records the 46 prior archives inspected, their Git blob identifiers, and file counts. The two main comparisons are the reflection-transfer and the CM/prime-bias packets.
* Published mathematical sources appear beside the arguments that use them in the PDF and TeX.

On systems with GNU coreutils, `sha256sum -c SHA256SUMS` verifies the supplied files before regenerating any of them.

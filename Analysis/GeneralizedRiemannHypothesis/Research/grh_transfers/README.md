# From Dirichlet GRH to class groups and prime races

Read **grh_transfers.pdf** for the full mathematical arguments. Its LaTeX source is **grh_transfers.tex**. All paths below are relative to this directory.

## Results

* The exponent-six census is complete for negative fundamental discriminants with at most six distinct prime factors, or with absolute discriminant divided by its largest prime factor at most 100,000,000. The first family has 429 fields, the union has 432.
* A weighted modulo-four prime race is strictly positive at every real scale above 3/4. The certificate covers its finite interval without floating-point arithmetic.
* The analogous eventual strict sign for the cubic of discriminant -23 is equivalent to its degree-two Artin Riemann hypothesis. A positive Mellin kernel bounds the contribution of zeros. Establishing that cubic sign at all large scales is an open step in the argument.

The input theorem is the Dirichlet GRH at commit 72fead102f663d5c7a407964a13dc0cf9d977207 of [lsernau/grh-lean](https://github.com/lsernau/grh-lean). The note identifies published mathematical and computational inputs, including the larger Elsenhans–Klüners–Nicolae census. The deductions in the paper were not formalized in Lean.

## Reproduce the finite checks

Python 3.9 or newer is sufficient. The scripts use the standard library. Do not pass Python's optimization flag, which would disable assertions. Redirect output to a temporary location when comparing with the supplied files.

| Command from the archive root | What it checks |
| --- | --- |
| `python3 checks/genus_thresholds.py` | Exact table-bin and endpoint inequalities for up to eight ramified primes |
| `python3 checks/check_exponent_six_cutoff.py` | Rational certificate for the cofactor bound |
| `python3 checks/check_exponent_six_fields.py` | Emits the CSV of 432 fields of exact exponent six through absolute discriminant 5,761,140. The summary goes to stderr |
| `python3 checks/check_exponent_five.py` | Emits the CSV of exponent-five fields among all fundamental discriminants through 250,000. The summary goes to stderr |
| `python3 checks/mod4_all_x.py` | Exact lower bounds at every breakpoint on the finite interval and an upper bound on the derivative of Dirichlet beta |
| `python3 checks/cubic_check.py` | Checks cubic Frobenius traces and computes the sample cubic and modulo-four integrals |

The two CSVs are computational outputs. The exponent-six CSV records class number, exponent, number of distinct ramified primes, largest prime factor, and cofactor. CSV entries use the negative field discriminant. The prime-race table in the cubic script uses floating point for illustrative values. Its exact root counts and the integer certificate for the modulo-four theorem are separate checks.

## Reproduce the source audit

The source check requires Git and an unmodified checkout. From this directory, run the following commands with the GitHub repository available.

```sh
git clone https://github.com/lsernau/grh-lean.git upstream
git -C upstream checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
python3 checks/check_source.py upstream
```

Compare the emitted JSON with `checks/source_audit.json`. The script checks the pinned tree digest, imports and target declarations. For a full Lean replay use the repository's pinned toolchain and instructions in either edition. The externally reported build, axiom, export and comparator checks used in this note are recorded by [Andrew Sutherland](https://math.mit.edu/~drew/shortgrh/).

## Rebuild the paper

Use a standard LaTeX installation with Latin Modern, AMS packages, enumitem, geometry, booktabs, xcolor, fancyhdr and hyperref. All references are embedded.

```sh
pdflatex -interaction=nonstopmode -halt-on-error grh_transfers.tex
pdflatex -interaction=nonstopmode -halt-on-error grh_transfers.tex
```

# A counterexample to McNew's geometric-progression conjecture

Open **report.pdf** for the complete research report. It begins with a human proof of a counterexample to McNew's Conjecture 7.2 on natural density. A smaller explicit example, an ideal-theoretic extension, separate upper-density bounds, and three investigations of the Lean formalization follow. The opening theorem requires no computer calculation.

## Reproduce the mathematical checks

From the directory containing report.tex run the following commands with Python 3.10 or later, with assertions enabled. Only the Stickelberger checker requires SymPy (tested with 1.14.0). The other verifiers use the standard library.

```sh
python checks/check_rankin.py
python checks/check_rankin_patterns.py
python checks/check_rankin_finite.py
python checks/density/check_density.py
python checks/check_stickelberger.py
python checks/sparse_places.py
python checks/check_frobenius.py
```

The two first checks examine the collision proof on finite models. The finite-witness script verifies the quantitative natural-density gain. The density subdirectory contains all 275 templates, interval witnesses and seven compressed proof trees for the upper-density bounds. Those certificates can be verified without an optimization solver. The cyclotomic script prints JSON giving exact gcds, least witnesses and congruence checks. Text outputs are included beside the corresponding scripts.

## Rebuild the paper

With a standard TeX Live installation, run `pdflatex report.tex` twice. All section sources are included. The prerequisites are standard LaTeX packages listed in the preamble. No bibliography processor or network connection is needed to compile or replay the certificates.

## Source comparison

The upstream revision is `72fead102f663d5c7a407964a13dc0cf9d977207` of lsernau/grh-lean. The ProveIt comparison uses `a1d43d8a32add57d596273e04648bc96a0a9bc0d`. The repository inventory and Git blob IDs are in `evidence/repositories.json`. The report distinguishes the earlier results on natural density and strict-sign Frobenius tests from its own results. The cited Lean build and independent kernel checks are upstream reports. This archive supplies proofs and exact finite checkers for the extensions without a new Lean formalization.

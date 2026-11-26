# Sparse equations for singular moduli and optimal tests for symmetric-power zeros

Open **report.pdf** for the ten-page paper. The master source is **report.tex**. Extract the full archive before rebuilding.

## Results

The lower relative density of rational prime conductors giving full support for singular moduli of the Gaussian field exceeds 99.9818260107372245%. This statement is independent of RH. The much narrower interval in section 2 bounds the density certified by the three tests. A second result determines the least Sato–Tate mean for a monic nonnegative character polynomial of even degree with its next coefficient prescribed. The paper proves a one-sided criterion for simultaneous symmetric-power RH and identifies the missing arithmetic inequality.

## Reproduce the checks

The density, finite-conductor and polynomial-weight verifiers require only Python 3.10 or later. The optional symbolic quotient calculation also uses SymPy. Run from the extracted directory:

```sh
python3 check_density.py
python3 conductors.py
python3 weights.py
python3 quotient_check.py
```

The matching outputs from this run are under **checks/**. The first program uses exact rational arithmetic to enumerate residue classes and bound the infinite tails. The second directly checks factorial valuations at prime conductors through 100,000. The third checks character identities at 100 degrees of the auxiliary polynomial and 500 parameter values. The fourth verifies the quotient equations at isogeny degrees three and five.

## Rebuild the paper

Run the following twice with pdfLaTeX in a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The source inputs are gaussian.tex, twoadic.tex, symweights.tex and analytic.tex. Original repository revisions and selected blob identifiers are in source-revisions.json. The references and links to prior reports are in the paper. The supplied research results have human-readable proofs. The accompanying checks are exact finite computations. No new Lean build or Lean formalization is claimed.

# Bertrand's postulate in intuitionistic primitive recursive arithmetic

Open **bertrand.pdf** for the proof. The same bounded search gives the least prime above each positive natural number. For all n ≥ 4 its value lies strictly between n and 2n − 2. The report also proves the usual endpoint variants and the consecutive-prime formulation.

## Contents

- **bertrand.pdf** and **bertrand.tex** contain the nine-page mathematical proof, its quantifier-free induction arguments, the finite prime certificate, and the Lean formalization guide.
- **lean/** contains a complete standalone Lean 4.19.0 proof over natural numbers. The public theorems are in **Bertrand.lean**. The verification transcript is **verification.txt**.
- **proveit/** contains a source-level client for the ProveIt iPRA derivation syntax, with the targeted commit, the exact remaining object-level obligation, and instructions for completing it. The client has not been built against its pinned Lean 4.32.0 workspace.

## Reproduce the checks

With Lean 4.19.0 available, run these commands from the directory containing this README.

~~~sh
cd lean
./check.sh
~~~

The script uses the standard library, builds a fresh set of modules, checks six concrete witnesses, and runs a dependency audit on the six public results. To use a particular Lean binary, set the environment variable LEAN to its absolute path. The checked public results list propext and Quot.sound.

To rebuild the report on a standard TeX Live installation, run the following from the root of the archive.

~~~sh
pdflatex -halt-on-error bertrand.tex
pdflatex -halt-on-error bertrand.tex
~~~

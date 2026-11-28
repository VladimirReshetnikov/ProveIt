# Four results extending ProveIt

Open **research-notes.pdf** for the four papers in one volume. Its first page links to each paper. Each subdirectory also contains a standalone PDF with live references and its complete LaTeX source.

| Directory | Main result | Proof and verification |
| --- | --- | --- |
| `anticodes/` | The diameter-three case of Kovačević’s root-lattice conjecture in every rank, with all equality cases. A multiset intersection theorem and a second extremal theorem for families outside every ball section. | `anticodes.tex` gives the reduction to finite graph inequalities. The Python and C++ programs independently prove the finite lemma, with full run records. |
| `egyptian/` | Full Hausdorff dimension of the set of targets for which every greedy prefix is uniquely optimal, with the joint Hausdorff and packing spectra of the approximation error. | `greedy-dimension.tex` gives a mathematical proof. The exact-rational program checks small examples, including competing representations with repeated denominators. |
| `li-kernel/` | The joint spectrum of the lower and upper decay of a Dirichlet Li heat density on every open arc. | `joint-spectrum.tex` specifies the analytic inputs from the repository. It also proves an unconditional spectrum for best Egyptian underapproximation errors. |
| `symplectic/` | The joint critical-window law for recovering an unknown nonsingular alternating form from observed isotropic subspaces. | `hidden_window.tex` gives the limit theorem and its wide-block extension. The program reproduces the numerical table and exact finite-field checks. |

## Relation to the repository

The source directory is [ProveIt at revision ff96fd44ab](https://github.com/VladimirReshetnikov/ProveIt/tree/ff96fd44ab160e65fb8a9d861243828d07c156cf/Analysis/GeneralizedRiemannHypothesis). In its article the starting points are the coefficient-collision and anticode discussion in `gpp.tex`, the decay estimates and spectrum question in `li.tex` and `rec.tex`, and the hidden-source-form question in `spn.tex`. References in the individual papers identify the arithmetic inputs and related work. The lattice, all-order Egyptian-fraction and finite-field theorems are independent of RH and GRH. The arithmetic interpretation of the Li result uses the stated critical-line estimates. These are research manuscripts for review.

## Reproduce the computations

From the extracted archive root, with Python 3.10 or newer and a GCC- or Clang-compatible C++17 compiler, run the commands below. The programs use the standard libraries. Keep Python assertions enabled.

```sh
python3 anticodes/check_diameter_three.py
c++ -std=c++17 -O3 anticodes/verify_diameter_three.cpp -o verify_diameter_three
./verify_diameter_three
python3 anticodes/check_anticodes.py
python3 egyptian/check_prefixes.py
python3 symplectic/verify_hidden.py
```

The two diameter-three programs use different vertex encodings and verification routines. Each checks the inequalities with integer or rational arithmetic. The other programs reproduce examples, counts and tables accompanying the written proofs. The included outputs allow line-by-line comparison.

## Rebuild the PDFs

With a standard TeX Live installation and latexmk, run from the extracted archive root

```sh
for paper in anticodes/anticodes egyptian/greedy-dimension li-kernel/joint-spectrum symplectic/hidden_window
do
  (cd "$(dirname "$paper")" && latexmk -pdf "$(basename "$paper").tex") || exit 1
done
latexmk -pdf research-notes.tex
```

The combined volume includes the four standalone PDFs in reading order.

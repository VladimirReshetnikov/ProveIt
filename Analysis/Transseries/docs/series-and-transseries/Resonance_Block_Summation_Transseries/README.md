# Resonance-Block Summation of Transseries

**Small divisors, coalescing Stokes actions, and nonlinear inversion**

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

Open `article.pdf`. Its editable, self-contained LaTeX source is `article.tex`.
Keep the `results/` directory beside the source when rebuilding: the source
inputs `results/coalescence_table.tex`.

The report studies the meromorphic Borel kernels

    Fhat(t) = t^d / product_j sin(pi omega_j t),  omega_j > 0.

Its main results are:

1. A uniformly normally convergent Stokes representation using blocks of at
   most d nearby pole occurrences, with explicit separation-independent norms
   and an action-cutoff tail bound.
2. The exact raw-residue convergence abscissa for two irrationally related
   lattices, including an explicit example where the raw series fails at
   every positive argument despite exact Gevrey order one.
3. Uniform coalescence profiles, exact double/triple residues, and a
   rational-exponential compression criterion.
4. Certified nonlinear inverse transport in the block norm, with separate
   action and amplitude truncation errors; a finite inverse coefficient
   formula at every action and its analytic finite-cut realization.
5. An abstract bounded-cluster criterion and twelve further research projects.

## Mathematical status

The report supplies conventional proofs. It does not claim Lean verification,
a named community-wide conjecture resolution, or established research priority
for every refinement. Classical Borel-Laplace summation, divided differences,
and Lagrange inversion are credited. The central contribution is a quantitative
finite-lattice/finite-cluster package, not a general theory of arbitrary
countable-action resurgence.

The comparison to ProveIt is specific: its weighted countable inverse theorem
requires a sum of individual analytic norms. In the present examples that sum
can fail even the term test. The report proves bounds after cancellation in
finite blocks, thereby supplying admissible data for the analytic inverse
method. It does not claim the general inverse formula itself is new.

The raw convergence boundary is not classified. The inverse's full Borel-sheet
structure, infinitely many period lattices, and global inverse univalence are
not claimed. The raw formal action expansion is not asserted to converge
numerically at fixed argument; the block-indexed representation is the
convergent one.

## Reproduce

Use Python 3.10 or newer and a TeX Live installation with the packages listed
in `article.tex`. The recorded run used Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0,
and pdfLaTeX.

```sh
python -m pip install -r requirements.txt
sh build.sh
```

The stages can also be run separately:

```sh
python verify.py --stage symbolic
python verify.py --stage numeric
python verify.py --stage tables
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The program uses no network access or external datasets. It writes generated
files only under the local `results/` directory. The build additionally creates
ordinary local TeX auxiliary files and logs.

## Executed checks

The distributed results record 36 exact symbolic assertions and 15 numerical
assertions, all passing. Contour checks use 90 decimal digits; near-collision
reference calculations use 200 digits. A separate 50-digit demonstration
compares the unstable raw residue formula with the stable pair formula.
Recorded values are rounded for serialization, not stored at full internal
working precision.

These checks are **not directed-rounding interval certificates** and do not
replace the mathematical proofs. The analytic tail bound is proved in the
article; its numerical evaluation in the script is ordinary high-precision
floating-point arithmetic.

## Contents

- `article.tex`, `article.pdf`: article source and rendered report.
- `verify.py`: complete symbolic and numerical checking program.
- `results/`: actual recorded checks and generated table source.
- `requirements.txt`, `build.sh`: dependencies and build command.
- `SOURCES.md`: repository and primary-literature provenance.
- `QA_REPORT.md`: compilation and visual-inspection record.
- `SHA256SUMS.txt`: checksums of all packaged files except itself.

No repository files were changed. No external source corpus or font files are
included.

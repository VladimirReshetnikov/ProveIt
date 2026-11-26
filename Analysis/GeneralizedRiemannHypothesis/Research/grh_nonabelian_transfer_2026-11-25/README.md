# Beyond Dirichlet GRH: optimal frames and an unramified nonabelian transfer

Research prepared for Vladimir Reshetnikov, 25 November 2026.

## Main results

The report analyzes the internal methods of `lsernau/grh-lean`, beyond familiar consequences of RH and Dirichlet GRH, and advances the nonabelian test case in the earlier ProveIt synthesis.

1. An exact integral frame of optimal positive integer bound **229**, with eight vectors, for the real S3 splitting field of `X^3-4X+1`. The previous explicit bound was 2,517,168. Optimality is for the bound, not the number of vectors.
2. A structural ramification obstruction to coprime frame bounds in the ordinary integer lattice.
3. Unramified cubic base change, preserving the source different, root discriminant, and fractional Weil lattice. An existing internal source theorem supplies compatible Weil data.
4. A proof that a self-dual projective Hermitian lattice over the relevant imaginary quadratic ring admits frames at **every sufficiently large integer bound**, containing prescribed vectors with prescribed minimum multiplicity.
5. A more permissive sufficient budget for the missing odd-cocycle estimate.

No further named open conjecture is claimed solved. The remaining tower-uniform frame estimate, correct raw-cocycle bound, and nonabelian prime-sum inequality are stated explicitly.

## Read and reproduce

- `report.pdf`: complete mathematical report.
- `report.tex` and `sections/`: exact LaTeX source of the PDF.
- `code/`: standard-library exact checkers and a PDF builder.
- `certificates/`: explicit frame matrices/vectors, a Hermitian polarization/reserve example, and check results.
- `evidence/`: source manifest, selected unmodified source files, static scan, prior-archive inventory and review scope.
- `formalization/Lean_port.md`: implementation plan, not a compiled Lean proof.
- `licenses/`: upstream license, notice and attribution files.

Run from this directory:

```sh
python3 code/reproduce.py
python3 code/build_pdf.py
```

The exact certificate checks need only Python 3's standard library. A conventional LaTeX installation can also build with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The PDF builder is reused, unchanged, from the preceding ProveIt synthesis. It supports a source-only TeX installation by generating a temporary local format; it does not modify the installed distribution.

## Evidence boundary

Source commit: `72fead102f663d5c7a407964a13dc0cf9d977207`.

ProveIt snapshot: `28ad287a8d13c0f864ebb51c7c053ad06aa6e585`.

The upstream Lean source was inspected and statically scanned. Its full build and independent kernel checks were not rerun. The new algebraic results have complete mathematical proofs and exact finite certificates, but no new Lean compilation is claimed. Numerical optimization was used only to find candidate integer frame vectors; the delivered checker uses exact arithmetic and does not need that optimizer.

The literature contains extensive work on integral sums of squares and Hermitian norms. This report claims a concrete advance relative to the inspected archive, not worldwide priority for every abstract lemma.

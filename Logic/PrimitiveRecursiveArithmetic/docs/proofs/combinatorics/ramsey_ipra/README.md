# Finite Ramsey's theorem in iPRA

Read **ramsey.pdf** for the mathematical argument, the explicit bounds, the infinite obstruction, and the implementation plan for an object-level derivation in ProveIt. **ramsey.tex** is the complete LaTeX source.

## Verified results

The Lean development uses Lean 4.19.0 and its standard library. `FiniteRamsey.finiteRamsey` proves the all-arity finite theorem. `Ramsey.MaskBridge.winner_correct` verifies the natural-number witness returned by bounded search. `exactRamsey_spec` verifies the least sufficient vertex count, and `counterColor_spec` verifies a counterexample coloring at each smaller count. The graph modules establish R(3,3) = 6 and R(3,3,3) = 17.

The human proof identifies the quantifier-free induction formulas needed in first-order iPRA. Quotation of those proofs into ProveIt's `Prf PRAAx` remains open. The alternative bound in equation (3) and the infinite counterexample are proved in the manuscript. The Lean all-arity bound uses equation (2).

## Reproduce

From the extracted directory, with Lean 4.19.0 and Python 3.10 or later on the executable path, run

```sh
sh verify.sh
```

The script compiles five modules, prints the axioms of the principal results and runs seven Python tests, including all two-colorings of the labeled graphs on five and six vertices. Temporary compiled files are removed on exit. To run only the small witness example, use `python3 code/ramsey.py`. To rebuild the PDF, run `pdflatex ramsey.tex` twice.

## Numerical conventions

Vertices are numbered from zero. Subsets are binary masks. A table digit at index `a` is the color of the subset with mask `a`, in base `max(2,q)` for `q` colors. A numeric certificate packs mask `h` and color `d` as `q*h+d`. Valid tables have digits strictly below `q`. The general primitive-recursive bound grows rapidly. The Python checker searches the supplied small input directly, while `bound_up_to` can compare the smaller bound with a chosen cap.

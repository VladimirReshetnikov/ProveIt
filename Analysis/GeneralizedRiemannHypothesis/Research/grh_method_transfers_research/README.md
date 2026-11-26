# Three transfers from the proof of Dirichlet GRH

Read `report.pdf` for the complete 16-page paper. The opening page has a linked reading guide. Section 1 concerns a published finite-ring question. Sections 2 and 3 solve a torsion selection problem posed in ProveIt. Section 4 develops sparse prime-sum and Li-coefficient results, including a rigidity theorem for arithmetic equivalence. Section 5 records the remaining questions.

## Main numerical examples

- Over the dual numbers over F₂ the natural-density supremum for three-term progression avoidance is between 7/8 and 119/128. The upper-density supremum is between 15/16 and 20/21. For the stronger condition of avoiding a pair with nonconstant scalar-square quotient, 7/8 and 15/16 are the exact two extrema.
- On the curve y² + πxy + y = x³, π⁴ = 2, exact order four has minimum blocking degree 5 and minimum fixed Gauss valuation 15/32 at zero tolerance and benchmark 1. The union of exact orders 8 and 16 has minimum degree 23 and budget 27/128. Both constructions attain both minima.
- For any two number fields with different Dedekind zeta functions the mean absolute difference of their Li coefficients tends to infinity over long consecutive windows, uniformly in the starting index. The proof makes no zero-location assumption.

## Reproduce the checks

Python 3.9 or later suffices and uses only the standard library. Run from this directory.

```sh
python3 code/check_finite_rings.py
python3 code/torsion_window.py --verify
python3 code/check_counts.py
python3 code/newton_counts.py code/order_four_counts.json
python3 code/torsion_window.py --low 3 --high 4
```

The text files in `code/` contain the original check outputs. The finite-ring script exhaustively counts small degree balls, tests the local square-divisibility conditions, and checks the disjoint collections of triples. Its large-cutoff pair densities are printed as decimals after exact rational computation.

The torsion code uses rational valuations. The shell calculation runs in quadratic time in the number of points of a shell. Explicit point enumeration grows exponentially with the upper order exponent. `newton_counts.py` accepts nested subgroup sizes in the JSON format illustrated by `order_four_counts.json`. Each row lists the valuation, number of points in the full subgroup, and number in the excluded subgroup, including the origin. The output includes each shell's required excess and minimum root count. The generic function `obstruction` can also take a finite test set with its own valuation and pair-distance functions.

`torsion_window.py --low L --high H --rho R --tolerance T` solves the indicated window on the example curve. It prints coordinates of roots for a monic extremizer in the compatible basis described in the paper. Use rational strings such as `1/8` for exact parameters. The arithmetic checks concern finite consequences. None of the analytic arguments relies on a zero table.

## Rebuild the paper

The master source is `report.tex`. Keep the accompanying TeX files in the same directory. A standard TeX Live installation with Latin Modern and the AMS packages suffices.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

## Sources and scope

- [Upstream Lean repository at the inspected commit](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207)
- [Published independent verification of both shortened editions](https://math.mit.edu/~drew/shortgrh/)
- [ProveIt incoming reports at the comparison commit](https://github.com/VladimirReshetnikov/ProveIt/tree/d31039a48d963692e5a5176f47b6603fc9e9d9cf/docs/incoming)
- [Asada and coauthors, original Questions 6.1–6.5](https://www.nathanmcnew.com/fqxramsey.pdf)

The source inventory records the Git blob hashes, sizes, and counts of TeX members for all 35 incoming ZIP archives at the comparison commit. The paper identifies the particular prior results it extends. The source and literature searches support a comparison with those reports; historical priority remains provisional. We inspected Lean source and used published verification records for the upstream build. The extensions in this package are ordinary mathematical proofs.

To check the files against the package manifest, run `sha256sum -c SHA256SUMS` from this directory.

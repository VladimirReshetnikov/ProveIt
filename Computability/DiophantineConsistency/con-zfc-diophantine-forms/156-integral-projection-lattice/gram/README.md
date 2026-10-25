# Exact Gram recombination of the direct ZFC-refutation quartics

All unknowns are unrestricted integers. Both equations are completely
specified ordinary quartics with fixed integer coefficients.

| Variant | Variables | Degree | Residual polynomials | Mixed residual products | Monomials | Height |
|---|---:|---:|---:|---:|---:|---:|
| balanced | 240 | 4 | 177 | 13 | 5,803 | 6,404 |
| lowheight | 240 | 4 | 177 | 7 | 9,357 | 4,160 |

For each variant, let r_i be the quadratic residuals listed in `equation.json`
and let `(i,j,s)` range over its `gram_cross_terms`. Its exact polynomial is

    Q(x) = sum_i r_i(x)^2 + sum_(i,j,s) s*r_i(x)*r_j(x).

`expanded_polynomial.json` gives every collected coefficient. A term
`[c,[i,j,...]]` denotes `c*x_i*x_j*...`; an empty monomial is a constant.
Residual indices and variable indices are zero-based.

The full proof is in `PROOF.md`. The new combiner is positive definite, so it
preserves the entire real zero set of the residual system. Composed with the
companion nonunit projection and the inherited direct C222 calibration, this
proves in ZFC that the polynomial has no integer zero exactly when Con(ZFC).
The finite checks below certify the new arithmetic objects and transformations;
they do not re-prove that inherited logical calibration or establish Con(ZFC).

## Reproduce and verify

Python 3.10+ and its standard library suffice. From this folder:

```sh
python3 -B build.py --check
python3 -B check_gram.py balanced
python3 -B check_gram.py lowheight
python3 -B -O check_gram.py balanced
python3 -B -O check_gram.py lowheight
```

`build.py` rebuilds in a temporary directory and checks all static output files
byte for byte. It reads only the local source equations and the frozen literal
edge lists in `EDGES.json`. Use `--output PATH` to retain a reconstruction in
another folder.

`check_gram.py` is independent of the builder and search: it checks exact
rational LDL identities, positive pivots, source hashes, every expanded
coefficient, variable liveness, all metrics, and two deliberately invalid
Gram certificates. Required conditions raise exceptions and do not rely on
Python assertions.

To evaluate the exact polynomial on a JSON array of 240 integers:

```sh
python3 -B evaluate.py --variant balanced point.json
```

This evaluator is not a solver or consistency test. It evaluates only the
tuple supplied by the caller.

The source equations in this component are copies of the matching newly
projected direct equations. The enclosing contribution retains their source
calibration, inherited licenses, and projection certificates. The optional
E8-lattice identification is descriptive; correctness uses only the explicit
rational factorization certificates.

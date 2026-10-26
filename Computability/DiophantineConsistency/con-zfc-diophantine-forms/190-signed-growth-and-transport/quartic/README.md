# Two new 209-variable quartics

The complete new semantic proof is `../report/signed_growth.tex`, with selected
inherited source proofs under `../inherited/pell210/`. `ALGEBRA_PROOF.md` covers
the subsequent exact affine elimination, integral scaling on zero sets, and
residual-basis changes. The semantic horizon replacement is not an algebraic
coordinate bijection with the old positive-square horizon.

The principal form is `equations/affine209_F64/equation.json`: 149 quadratic
residuals in 209 unrestricted integer variables. The equation is their sum of
squares. Its full collected expansion has 5,486 monomials and exact height 2^32.

The second principal form is `equations/affine209_F128_basis/equation.json`:
149 quadratic residuals, 6,654 collected monomials, exact height 2^30.
The F128 form without the basis change is a retained intermediate.

Run `python3 -B verify.py` for independent exact checks. Run
`python3 -B code/build.py --output /tmp/conzfc-quartics-rebuilt` with a fresh
output directory to reproduce the files. The root `verify_all.py --rebuild`
performs these checks and byte comparisons automatically.

In each sparse term `[c,[i,j,...]]`, the second entry is a sorted list of
variable indices with repetition; the term denotes `c*x_i*x_j*...`.
An empty list denotes a constant. The supplied final polynomial data uses
the same format. All coordinates are independently quantified integers.

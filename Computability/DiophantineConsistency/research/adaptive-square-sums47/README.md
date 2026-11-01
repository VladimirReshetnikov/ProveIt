# Forty-seven-variable quartic candidate

This 179-operation graph substitutes the linear expressions
`eta + ySumVariable` and `productVariable2 + Y` for the 49-variable parent’s
`cVariable` and `aVariable`. Both expressions are positive when the remaining
unknowns are positive. It removes the two corresponding squared residuals and
their accumulation gates. The remaining 33 residuals are quadratic, so the
sum has exact degree four. `generate.py` pins the parent, verifies the changed
rows, and checks all inputs and gates are live and topologically ordered.

`verify_substitution.py` independently expands the residuals as exact sparse
integer polynomials, checking that every parent residual specializes to its
candidate counterpart and both omitted residuals become zero. The exact
degree and positive-shift checks are finite computations, not Lean degree
theorems. The substitution calculation is not a proof of zero-set equivalence
in all models: the converse requires recovering the two coordinates and the
relevant positivity and sum-of-squares arguments.

**Open:** the 47-variable graph has not yet been bound to a Lean literal; its
model equivalence, native iPRA endpoint and guarded replays remain to be proved.
There is no global minimality claim.

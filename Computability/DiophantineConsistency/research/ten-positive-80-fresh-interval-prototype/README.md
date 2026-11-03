# Fresh unscaled Pell interval from an 80-graph zero

`TenPositive80FreshInterval.graph_fresh_interval` assumes an actual positive
80-graph zero and the symbolic β/low/high port equalities in an IΣ₁ model.
It produces a single r with `rankNat = 2*r+1` and constructs the unscaled
source Pell pair

    K = 2*ycoord (r+1) (2*(X*Y*Y-1)+1)
    C = ycoord (2*r+1) (Y*(X+1))

and proves `K*Y < C < K*(Y+1)`. Here X and Y are the actual 80-graph
values, but this fresh unscaled C is not identified with the graph's scaled
ordinate. The proof gets a shared small-remainder split from the scaled graph
sandwich and applies the existing unscaled Pell sandwich to transfer the
integer floor. The upper unscaled estimate uses a crude bound derived from
the split, avoiding an assumption that the desired fresh interval holds.

This establishes a necessary building block for source reconstruction, not
an old graph solution, halt equivalence, literal PDF binding, or iPRA proof.
The guarded check is `observations/fixeddigits-attempt01/`; object
`/tmp/tenpositive-80freshinterval-hsjp99r3/Direct80FreshInterval.olean`,
SHA-256 `835e3f116ff9b92a3b8bdb67afbc3b3cc99a6843b576a7a045f85ad8769a1019`.
The receipt records selected direct input pins and resources; it inherits the
usual project/package, dynamic-library and transitive source-object limits.

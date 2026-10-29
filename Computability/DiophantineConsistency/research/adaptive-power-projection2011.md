# Adaptive main correction and the X lower bound

From the actual adaptive zero, the oriented main-root identity and exact
first-index quotient imply `q | 3X`, and hence `q ≤ 3X`, in every selected
`IΣ₁` model. The proof uses `Y=q³s` to show that the correction
`4XY²t` is divisible by `U=q²Y`, then cancels the positive factor `qY` in
the main-root equality. The remaining coefficient `H=3+4Y(X+1)` is
`3 mod q`. No `q | X` or power representation is assumed.

For the actual radix-47 port, `β ≥ 46` and a positive shifted J give
`q ≥ 47`, which makes `q ≤ 3X` imply `X ≥ 16`. This supplies the size
premise of the existing internal Pell growth argument. It does not yet prove
`Y > 2^R`, the corresponding main-coordinate projection, or `X = 2^R`.

# Checked coefficient bounds for split homogeneous layers

[`SplitCoefficientBounds.lean`](Lean/DiophantineConsistency/SplitCoefficientBounds.lean)
proves a uniform bound for

```
P=encoded(w,y)^2*D2+encoded(w,y)*D1+D0.
```

If each coefficient of each kernel has absolute value at most `H>=0`, then
for every index, including unmonitored indices,

```
|P.coeff n|<=H*(S^2+S+1),  S=sum_i |y_i|.
```

The quadratic layer reuses `SelectiveCoefficientBounds`; the linear layer
sums the monomial convolution bounds. Triangle inequality adds the three
layers. No distinctness of the weights, target isolation, source identity,
coefficient sign, or kernel degree is assumed.

For `d` natural coordinates with `y_i<=b` and `b>0`, the bound becomes
`(d^2+d+1)*H*b^2`. Thus 31 coordinates give exactly `993*H*b^2`.
The digit coordinates may be zero. The estimate also covers the positive
source coordinates `y_i=z_i+1<=b` used by the sparse decoder.

For `H>0`, `t>=2`, and a possibly rounded-up base satisfying
`4096*H*b^2<=2^t`, the strict inequality `993<1024` gives

```
|P.coeff n|<2^(t-2)=2^t/4.
```

Both forms are exported, so the division form feeds
`SparseBorrowCarry.tau_polynomial_iff` directly. The scale is a numerical
hypothesis, not a choice or an imported source-calibration premise.

Regression checks deliberately put all 31 coordinates at the same weight.
The constant coefficient then attains `993`, including a signed-coordinate
example whose coefficient is `-993`. Further checks include `b=1` and a
rounded-up base. All audited proofs use only the standard Lean axioms.

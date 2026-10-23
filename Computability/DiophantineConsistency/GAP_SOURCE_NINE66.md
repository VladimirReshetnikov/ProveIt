# Unbounded H2082 source equivalence in nine coordinates

[`GapSourceExistence66`](Lean/DiophantineConsistency/GapSourceExistence66.lean)
and [`GapNineSource66`](Lean/DiophantineConsistency/GapNineSource66.lean)
remove the digit bound from the H2082 source contract. Their endpoint is an
arithmetic equation with exactly nine natural coordinates, equivalent to
the existence of a positive common zero of the literal 22-row gap source.
The four coefficient ports retain their explicit size hypotheses.

For the coherent compact54-sharp port bounds, the half-height parameter is
`a=432007`. The resulting source registers, in positive coordinates, are

```
B = 2^864026*b^2
ell = sum_r B^(weight_r)
targets = sum_t B^(target_t)
Gs = D2(B)*(ell+g)^2 + D1(B)*(ell+g) + D0(B)
S = g+B^117*(2*Gs+targets)
T = B^117-1-(b-1)*ell+B^117*(B-2)*targets
L = b*B^2200
R = L*(S+T+1)-S-1
N = 2^6480184*B^1162
t = b*B^116.
```

`D0,D1,D2` are the 6/36/43-record kernels in `GapKernelData66`, with the
H2082 weights and targets from `GapCertificate66`. The checked
`FreeCarrierRatio` finalizer uses `R,N,b,g,t` and the remaining coordinates
`h,s,w,C,i,j,n`. The public positive tuple contains `j_plus`; internally
`j=j_plus-1`. The natural tuple shifts the other eight coordinates by one
and uses its `j` coordinate directly. Those registers abbreviate a single
equation and introduce no additional unknowns.

`hasZero_iff_source` uses the same explicit cofinal construction as the
earlier split proof: for a source digit tuple `z`, set
`b=2^(sum_r z_r+1)`. Its digit sum is below `b`, which also bounds the sparse
code by `b*B^116`. This supplies the stronger cap needed for finalizer
completeness. In the other direction a zero first supplies the power-of-two
base and weak cap, then the checked carry contract decodes the source.
No boundedness or no-carry premise survives the existence theorem.

`GapNineSource66.exists_natural_zero_iff_source_compact54` specializes the
result to the complete four port boxes. A literal source row at the all-one
tuple is -7, so any source zero has a nonzero digit and supplies positive
`g`; that condition is derived rather than assumed.

`source_successor_zero_iff_old` composes the actual affine positive-source
equivalence with explicit successor/predecessor coordinate maps. Under
`beta>0`, `compact54_zero_iff_split59` therefore proves the H2082 equation
and the earlier split116 arithmetic equation have equivalent unbounded
natural zero existence. Their full positive coordinate conventions agree.

The dedicated checks audit all thirteen new endpoints and the CRT-coordinate
translation. Only Lean's standard axioms occur. The subsequent
[actual nine-variable polynomial binding](GAP_NINE_POLYNOMIAL66.md) now also
passes Lean, as do the [443/450-operation literal circuit identification](GAP_CIRCUIT_RECIPE66.md)
and [degree upper bound](GAP_DEGREE66.md). Authentic native source-to-refutation
calibration and the internal object-language ZFC equivalence remain open.

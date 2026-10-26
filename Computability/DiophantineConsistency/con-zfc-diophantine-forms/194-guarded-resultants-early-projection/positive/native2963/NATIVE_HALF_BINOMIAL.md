# Native half-binomial and mask population

`NativeHalfBinomial.source_half_binomial` closes the half-binomial arithmetic
step for the literal old-z source:

```
R=2r+1, r≥12, 2Y=choose(2r,r)+wX.
```

Its premises are positive source coordinates, all22 literal source rows,
`NativePellBootstrap.PortBox` and `beta≥15`. No parity, exponential identity,
ratio estimate, binomial identity or common-scale premise is supplied.

The proof adapts the existing `Ratio90.upper_key` and
`Ratio90.one_add_pow_le` estimates to the actual doubled first coordinate.
With `xi=(X+1)^(2r)/X^r`, it proves

```
xi/2 < c/k < xi/2+1/2.
```

Both sides of the source interval `Y<c/k<Y+1` are exact consequences of
`c=kY+eta`, `k=eta+zeta` and positive `eta,zeta`. The existing binomial-tail
theorem supplies the integer part of `xi`; its central coefficient and the
power-of-two base are even. The two strict intervals therefore recover
twice `Y` exactly. The analytic error bound uses `72r<X+1`, derived from
the already recovered `X=2^(2r+1)` and `r≥12`.

`NativePopulationLower.source_population_lower` then proves

```
3u+2 ≤ sigma_2(R)     when q=2^u.
```

The source gives `q³|Y` and `3u<R`, so `2^(3u+1)` divides both `2Y` and
`X`. The exact half-binomial equation transfers this divisibility to the
central binomial coefficient. Existing Jones1982 Lemma2.15 and the odd-rank
population identity yield the stated bound.

`NativeMaskPopulation` supplies the local decoding step. If the rank has
the explicit four-block expression

```
R=(A+M)+2^u(F+H)+2^(2u)(2^u−1−A)+2^(3u)(2^u−1−F),
```

with `A,F<2^u` and `sigma_2(M)+sigma_2(H)≤u+2`, the source lower bound forces
`A AND M=0`, `F AND H=0` and exact population `sigma_2(R)=3u+2`.
No absence of block carries is assumed: the proof starts from the general
population subadditivity bound and derives the vanishing overlaps by
saturation.

The same module proves the exact repeated-mask population for radix `2^d`
and positive repetition count `N`. If `MC,MF<2^d`, `MC` is even,
`MF=4(mod8)`, `d≥3` and their populations add to `d`, then the all-one
radix word `J` satisfies

```
sigma_2(MC*J+1)+sigma_2(MF*J−1)=d*N+2.
```

The increment/decrement corrections are proved from the displayed low-bit
congruences. The subsequent [binding to the complete literal source](NATIVE_SOURCE_WINDOW.md)
now passes Lean. The native convolution/window decoder and K215/refutation
theorem remain separate. No fixed-payload calibration or object-language
ZFC equivalence is asserted by these local results.

Dedicated checks audit all public theorems with only the standard Lean
axioms `propext`, `Classical.choice` and `Quot.sound`.

# H2082 numerical source-word bounds

`GapWordBounds66` proves the new source positivity and packing estimates.
Its kernel contract requires degree ceilings1627,1941,1850, a common
coefficient height `H`, and coefficient1 at quadratic degree1850. The proof
reuses the existing generic geometric-series and low-mask estimates. The
negative-layer gaps are25 and455, which establish strict source positivity
for every nonnegative code candidate before either decoding or a source zero
is assumed.

Under `B=4096*H*b^2`, `H>0` and `b>=1`, the weak cap
`g<4*b*B^116` supplies the complete low/high packing bounds:

```
0 < sourceValue;
g < B^117;
0 <= lowMask < B^117;
0 < S; 0 <= T;
S+T < B^2200;
S < b*B^2200.
```

The high-word block length is2083, because the source-product degree ceiling
is inclusive at2082. Its target exponents are at most2050.

`GapSourceWords66` connects these integer bounds to the actual natural word
and mask definitions used by `GapNineRatio66`. The exponent `a` is half the
coefficient-height exponent: `H=2^(2*a)` and
`B=SplitNineRatio.base (2*a) b`. `highInt_pos` justifies conversion of the
polynomial high word to natural data on every nonnegative outer assignment.
`word_cast`, `mask_cast` and `rank_cast` give the ordinary integer-polynomial
formulas before a finalizer zero is known. `weak_cap_bounds` supplies the
reduced rank's required word range.

`literalParameters ports` supplies the actual H2082 weights,22 targets and
three kernels already bound to `GapSource66.rows`. `literal_valid_pow`
discharges its validity contract from the four ordinary nonnegative port
bounds, widths `p,q` with `p+4<=q`, and `p+q+1=2*a`. The sharp whole-tuple
widths429959 and434054 therefore give `a=432007`, the radix scale exponent
864026 and the threshold scale exponent6480184. The check file instantiates
this arithmetic identity without materializing the large payload integers.

Dedicated checks audit every public numerical and cast theorem. Only Lean's
standard axioms occur. No source zero, digit decoder, native compiler
calibration or internal ZFC consistency statement is used to establish these
word bounds. The subsequent [carry/source equivalence](GAP_SOURCE_CONTRACT66.md)
and [unbounded source existence](GAP_SOURCE_NINE66.md) now pass Lean.
The counted443/450-operation DAG identification remains a further bridge.

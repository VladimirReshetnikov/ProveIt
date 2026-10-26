# Strict local ranges and pooled powers on the diagonal source

This is a composition of existing, explicitly attributed arithmetic
mechanisms with the newly supplied affine radix `q=6z+3`. It does not claim
priority for diagonal growth, linear beta bases, strict local bounds, or
two-row pooling. The complete parent is the 238-variable diagonal source
under `../diagonal238/`, with its ordinary proof
in that construction's `PROOF.md`. The old pooled-power and strict-horizon
lemmas are from the pinned incoming `ConZFC_Pooled_Powers_2026-10-25`
archive. All final quantified coordinates are unrestricted integers.

The literal composition has 223 coordinates and 160 quadratic residuals.
It is an input to separately certified changes of variables and monic
projections. Such subsequent exact integer transformations do not require
changing this semantic proof. The parent C222/ZF/ZFC refutation calibration
is explicitly inherited; no new end-to-end Lean/Rocq compilation is claimed.

## 1. Strict ranges remove the derived power

The parent has `t=16+2h^2`, `F=t^t`, binomial shift `R=F`, and
`y=F(2v+1)`. Its four local schema parameters and its local derived-label
sum are bounded by `t` using five divisibilities `N|binom(a,t+1)`.
Tighten these five lower binomial indices to `t`. The encoded row index
already uses `t`; accumulator and quotient ranges are unchanged.

Soundness is immediate once these binomial ranges are interpreted: they
impose the stronger local bounds `0<=a,b,c,d,J<t`, within the parent's
permitted box. In particular the same local-polynomial majorant, prime-power
row selector, positive-weight flow extraction and diagonal large-evaluation
lemma apply. This concerns the small decoded local value of `J`; its global
CRT value is still the deliberately large semantic Pell anchor.

For completeness, start with a finite proof tree and its finite set of
parameter tuples, including the truth-padding tuple. Choose the even
cofinal horizon `t=16+2h^2` strictly above their parameters, every full local
derived-label sum, and the number of tree steps. This choice precedes `F`,
the pending-state products, `y`, and the beta code. The parent's precision-
`N^2` CRT construction is unchanged. At every prime power `p^(ex)` in `N`,
a target value `w<t` is attained modulo `p^(2ex)`; the falling factorial
for `binom(a,t)` contains the factor `a-w`, unless the binomial is zero.
Division by `t!` loses at most `t-1<x<=ex` valuation. Thus the required
`p^(ex)` divisibility holds. Polynomial congruence gives the same statement
for the derived label. No fixed old horizon is required to be preserved.

All five ranges now use the existing normalization ratio `M/q^t`. Delete
the old ratio `M/q^(t+1)`, the output `q^(t+1)`, its power quotient, and
the private discriminant wire used by its derived one-step Pell pair.
The exact consumer sets are recorded in the strict certificate. There are
four deleted coordinates and three deleted residuals. In the original
square frame delete only the square of the discarded output. Its independent
principal pair did not exist: the pair was derived from the retained pair
at `t`. Every actual atom for every surviving request remains framed.
The redundant atom `t+1` may remain in the frame and causes no difficulty.

The result has 234 coordinates and 171 quadratic residuals. This is a
semantic change with a fresh canonical completeness map, rather than an
integer-coordinate bijection with every old parent zero.

## 2. Two rows suffice for a block at a fixed nonzero base

Let `W>=258`, `|A|>W^W`, and let there be at most 15 requests at a common
nonzero integer base `n`. For every request let `X_i,Y_i` be the canonical
signed Pell coordinates at signed index `k_i`, and let `Z_i=A Y_i`.
Assume that the frame gives `n^2,m_i^2,k_i^2<W` for the base, proposed
output and index. Set

```
T = 2An-n^2-1,
D_i = m_i-X_i+Z_i,
H = sum_i Y_i(m_i-X_i),
S = sum_i(D_i^2-Y_i^2).
```

These are proof abbreviations. Add only two integer coordinates `K,L` and
the two quadratic residuals

```
K - 2H - (2A-n)L = 0,
S - nK + L = 0.
```

Eliminating `K` mathematically yields `S-2nH=TL`. Direct expansion, using
only the retained equations `Z_i=A Y_i`, gives

```
sum_i(D_i-nY_i)^2 = S-2nH-T sum_i Y_i^2.
```

Hence `T` divides the sum of squared Pell-power errors. Put
`b=floor(sqrt(W-1))`, so `b>=16` and every absolute base, output and index
is at most `b`. Since `T=-1 mod n`, the Pell group congruence is valid for
negative indices as well. Multiplication by `n^(2b)` shows that `T`
divides the ordinary nonnegative integer

```
Eerr = sum_i (m_i*n^b-n^(b+k_i))^2.
```

Every exponent here is nonnegative. Each squared term is at most
`4 b^(4b)`. Consequently, with `r<=15`,

```
0 <= Eerr <= 4r b^(4b) < W^(2b+1) <= W^W.
```

The strict inequality uses `4r<=60<W` and `b^2<W`; the last uses
`2b+1<=b^2+1<=W`. On the other hand,

```
|T| >= 2|A||n|-n^2-1 >= 2|A|-W > W^W.
```

Thus `Eerr=0`, and every requested power is exact. If `|n|>=2`, a negative
index would give `m_i*n^(-k_i)=1`, impossible in integers. Therefore all
such indices are nonnegative. The lemma also covers unit bases with their
signed-index outputs, but the present application needs only nonunits.

Conversely, canonical exact powers make each `D_i-nY_i` divisible by `T`.
The displayed identity makes `L=(S-2nH)/T` integral, and the first row
defines integral `K`. Thus the two new rows preserve zero existence under
the stated retained-frame and canonical-pair hypotheses. The powers, `b`
and the quotient expressions occur solely in the proof, not as primitives
of the final polynomial.

## 3. Literal instantiation

Apply the lemma to eleven requests at `q+1` and three requests at `q`.
All 14 retained `A Y` gates and principal Pell norms are checked literally
by the producer and independent checker. The existing coordinate offsets
are essential: every stored `X` has actual value `X+1`, pair 3 has actual
ordinate `Y-1`, and pair 12 has actual `A Y` value `Z+1`.

The parent already eliminated the separate modulus for `q`; its exact
affine restoration in terms of the remaining modulus is

```
T(q) = T(q+1)+2q-2A+1.
```

The checker authenticates each old congruence using this actual expression,
rather than assuming that an absent coordinate is present. Pooling removes
the fourteen private quotients and the one remaining modulus, and adds four
coordinates. Thus it saves eleven coordinates and eleven residuals, giving
223 coordinates and 160 residuals from the strict 234-coordinate source.

The original square frame, lower Pell scale, semantic anchor, all indexed
principal norms, all `A Y` rows and the complete signed-orientation pool are
retained. Their ordinary proofs precede every exact-power interpretation.
Consequently they still give canonical signed pairs and `|A|>W^W`.
The frame has the same positive sum of affine squares, with only the deleted
output square removed; `t^2` remains, so `W>=2+t^2>=258`.

## 4. Sign recovery after pooling

The affine radix makes this composition particularly direct. For every
integer parameter `z`,

```
q=6z+3,     |q|>=3,     |q+1|>=2.
```

Thus both pooled blocks may be interpreted immediately after orientation,
before using any sign of `B`, any factorial claim, or any semantic meaning
of the CRT representatives. They recover all nine representative signs,
`x>=0`, `y+1>=0`, and the exact denominator powers. The retained individual
power at base and exponent `t` gives `F=t^t>=2^64`. Therefore
`y=F(2v+1)` and `y>=-1` force `y>=F`.

The retained index row `B*index_quotient=C0+F+1` gives `B!=0`, and
`H=3+6 sum(a_i)>=3`. Its individual self-power gives
`q=(BH)^x`; since `q!=1`, `x>=1`. The beta endpoints then give
`x>=F+1` and `x>=2+(t+1)y`. This is stronger than the early bound `x>=t`
needed after removal of the `t+1` request. Thus there is no lost bootstrap
premise from tightening the ranges.

The signed first-binomial remainder argument is unchanged and yields
`B=binom(F+t,t)>F+1`, so `C0>=1`, `B>0`, and `q>0`. The individual
request at base `B` can now be interpreted as `N=B^x`. The common remainder
norm still gives all eleven centered residues, now with the five tightened
ranges using denominator `q^t`. Their genuine low remainders have at least
the previous strict margin. The bounds
`2+t+x+y+F<2x`, `(2x)^(2^23)<2^x`, and `2^22(t+1)<x` still hold.

The inherited binomial prime-power selector for shift `F=t^t` therefore
recovers every actual local row. The existing late zero-path contradiction
excludes `y=F`, then the positive accumulator product and diagonal
large-evaluation argument extract exact label multiplicities and a finite
C222 refutation. This proves soundness.

For completeness use the stricter cofinal horizon from Section 1, construct
the same factorial-free CRT witnesses, positive radix and canonical Pell
pairs as in the parent, and replace the removed individual quotients with
the four pooled coordinates supplied by Section 2. All parity conditions
remain exactly those of the parent: `B` is odd, `H` is odd and divisible by
three, hence `(BH)^x=3 mod 6`. No parity of `x` is required.

## 5. Logical conclusion and verification boundary

The pooled source has an integer zero exactly when the calibrated finite
C222 calculus has a refutation. The inherited unconditional ordinary
interfaces `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` compose with these
maps. Therefore ZFC proves that the sum of squares of the literal 160
quadratic residuals has no integer zero if and only if `Con(ZFC)`.

All new source transformations and exact finite coefficients are provided.
Independent finite checks do not replace the unbounded sum-of-squares
estimate, the sign-order argument, or the inherited logical calibration.
Subsequent integer-bijective radical projections and row-basis changes may
be composed without modifying this theorem.

# Independent review of the replacement source in the ten-integer wrapper

Reviewed the source definitions in `CHANNEL_PROOF.md`, the literal `ten()`
construction in `../build.py`, and the inherited wrapper and its stated
dependency contract in `../upstream/wave7_sun_popcount.tex`. This is an
ordinary mathematical review of the replacement source and its interface.
It does not independently reprove the inherited Sun bridge and does not
provide a proof-assistant certificate for the final consistency theorem.

## The stronger range bound

The Sun source requires the sum of the two codes to be smaller than its
block size. The separate bounds `Sc<L` and `Tc<L` do not establish this.
The stronger assertion does follow from the source estimates.

Write `W=108`, `Q=1914`, `K=2131`, `E=2241`, `H=2372`,
`N0=B^(W+1)`, `Z=B^(K+1)`, and `L=N0*Z=B^E`. For `b>=2` and
`0<=g<4bB^W`, the established bounds are `g<N0`, `0<=Mc<N0`, and
`0<F<52b^2 B^K`. Since the target exponents are distinct and lie in
`[0,Q]`,

```
(B-1)At <= B^(Q+1)-1 < B^K.
Jc+(B-2)At = 2F+(B-1)At < (104b^2+1)B^K < Z/4.
```

The last inequality uses `B=base_scale*b^2`, `base_scale>420`, and
`b>=2`. Consequently

```
0 <= Sc+Tc < 2N0 + N0*Z/4 < N0*Z = L,
```

where the final strict inequality holds for `Z>=4`.
This supplies the nonoverlapping block condition for
`X=L^2+(Sc+Tc)L+L-1-Sc`.

## The Sun branch and congruence

The inherited finalizer recovers `b=1+3f` as a positive square and
`O>0`. Since `O=f^2*l^2*Delta`, necessarily `f!=0`; thus `b>=4`.
Its recovered range `0<g<2cap`, with `cap=bB^108`, lies inside the
range above. The source estimates therefore apply throughout the
reverse-bridge branch.

The fixed exponent `kappa` is even, so `base_scale=2^kappa` is `1`
modulo `3`. As `b=1` modulo `3`, also `B=N0=L=1` modulo `3`.
The definitions give `Mc=0` modulo `3` and, because there are exactly
22 target positions, `At=22` modulo `3`. It follows that
`Tc=-22=2` modulo `3`, and hence `X=1+Tc=0` modulo `3`.

For `g>=0`, the globally positive carrier gives `Sc>0`; the mask
gives `Tc>=0`. Therefore `X>=L^2>3b`. The threshold and cap are
positive monomials of the same form as in the inherited contract:

```
cap = 2^(108*kappa) * b^217,
Y   = 2^(2372*kappa-21) * b^4713.
```

In particular `Y>max(b,256)` on this branch. Forward witnesses can
choose square powers of two `b=4^s`, as large as required, and the
parent coding supplies `g>=B>=b` and `g<cap`.

## Exact population calibration

On the recovered binary branch, put `b=2^k` and `B=2^v`, where
`v=kappa+2k`. The 31 free digit positions give

```
pop(Mc) = (W+1)v-31k.
pop(Tc) = (W+23)v-31k-22.
```

The established sum bound separates the three blocks of `X`, so

```
pop(X) = 1+E*v+pop(Tc)
         - [pop(Sc)+pop(Tc)-pop(Sc+Tc)]
       = H*v-31k-21-carry_defect.
```

The nonnegative carry defect vanishes exactly when `Sc & Tc = 0`.
The literal builder uses

```
Y = base_scale^15 * 2^(kappa-21) * B^(H-16) * b.
```

Its binary logarithm is
`16kappa-21+(H-16)v+k=Hv-31k-21`, exactly the required population
threshold. Thus `Y` divides `binomial(2X,X)` exactly when the source
codes have no common set bit. The old requirement `Y=N^2` is not an
assumption of the packaged Sun contract.

## Scope of the conclusion

No change to the Sun bridge, interpolation step, positivity finalizer,
weighted square merger, or three-radical norm is required. The displayed
`ten()` construction retains those formulas. The replacement source
satisfies the same wrapper hypotheses after the summed range estimate
above is supplied. No blocking mathematical issue was found in this
source substitution.

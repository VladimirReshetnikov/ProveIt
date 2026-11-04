# Conditional first-index-three arithmetic obstruction

This is an exact **ordinary-integer scalar certificate**, not a Lean theorem and not a graph-zero or fixed-port claim. Let `X≥32`, `Y≥1`, `A=X+1`, `P=XY²`, and

```text
k = 32P²+32P+6
c = 16(AY+1)⁴−12(AY+1)²+1.
```

The Pell recurrence gives these formulas when the first ordinate index is 3 and the main ordinate index is 5. If additionally `kY<c<k(Y+1)`, the polynomial certificates below imply

```text
X²+4X+4 < 2Y < X²+4X+8.
```

If `q≥32`, `X=q*w` and `Y=q³*s` for natural `w,s`, then `2Y−X²−4X` is a multiple of `q` strictly between 4 and 8, a contradiction. The first-index 3 to main-index 5 inference uses the separately checked `n<r<2n` and oddness; the present checker does not bind those hypotheses, the carrier inequalities, or the `X,Y` coordinates to an actual 74 graph zero.

For the lower endpoint, let `D=A⁴−2X²Y`, and suppose `2Y+w=X²+4X+4`, `w≥0`. The checker verifies the exact identity

```text
c−k(Y+1) = 16Y⁴(X²w+4X+1)
  +32(2X³+6X²+5X+2)Y³ +(84X²+136X+84)Y²
  +40XY+34(Y−1)+33.
```

The right side is strictly positive for natural `X,w` and `Y≥1`, contradicting `c<k(Y+1)`. The checker actually verifies an identity with the residual `X²+4X+4−2Y−w`, so it does not assume the equality while performing the polynomial calculation.

For the upper endpoint, if `2Y=X²+4X+8+w`, `X=32+u`, with `u,w≥0`, write `t=2Y` and `z=(X+1)t+2`. The denominator-free identity is

```text
kY−c = X²t⁵+4Xt³+3t−z⁴+3z²−1.
```

After those substitutions its sparse polynomial in `u,w` has 46 terms, **every coefficient strictly positive**, including the constant term. Thus `kY−c>0`, contradicting `kY<c`. The checker derives the third and fifth Pell ordinate polynomials by recurrence, verifies both identities and the symbolic substitution exactly, checks every upper coefficient and the `q`-divisibility factorization, and performs a few integer cross-checks. No numerical search is used to justify the universal sign argument.

Run `python3 -I -S -B research/trace74-first-index-three-obstruction/check.py` from the `Computability/DiophantineConsistency` directory. The receipt records source and output hashes; the checker rejects missing isolation/no-site flags and optimized Python. The [independent arithmetic audit](../../reviews/trace74-first-index-three-obstruction-independent/README.md) independently expanded both polynomial certificates and checked the strict interval and divisibility argument. Formal model-arithmetic transfer, graph binding, Lean checking, provider ancestry and the unrestricted 74/75 question remain separate.

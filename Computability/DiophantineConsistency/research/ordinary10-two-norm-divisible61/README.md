# A 61-operation divisibility presentation of the shifted two-norm graph

`candidate.json` is a 10-variable, 61-live-operation Diophantine equation over natural inputs and four fixed natural ports. Under **beta>0 and K0>0**, its standard-integer zero existence is equivalent to that of the [9-variable, 64-operation shifted two-norm graph](../ordinary9-shifted-free-aux-two-norm64/README.md). The equation has exact degree 60 for any fixed beta≠0. It remains a reduction of the relaxed free-y² child: the reverse bridge to the original 85-row parent and any Con(ZFC) or iPRA equivalence remain open.

The first/main coordinates and all main-residual rows are unchanged. The old natural r input is replaced by two natural inputs h and tau. With `b=beta*J`, actual first carrier `B=C*(X+K0)−F`, and `ell=XY²k`, the new equation is

```text
(B−b*h)² + (tau²−(1+ell*(ell+k)))² + A1² = 0.
```

The sum is zero exactly when all three integer residuals vanish. It uses one additional variable but saves three binary operations compared with the 9/64 graph.

## Preliminary consequences of either graph

For either a 9/64 zero or a new 10/61 zero, `A1=0` implies **X>0**. Indeed `q=1+beta*J≥1`, `Y=q³s>0` and `U=Yq²>0`. Square divisibility makes the signed main root `Dstar=U*d` for some integer d. If X=0, then `a=Y`, `H=4Y+3`, and the literal root equation yields `H | U*(d−a*c)`. Its norm gives `(d−a*c)*(d+a*c)=1+Hc²`, so `d−a*c` is invertible modulo H and H divides U. Hence H divides `4U=q²(H−3)` and also `3q²`, impossible because `H≥4q³+3>3q²`.

The old graph has J>0: if J=0, then q=1, `C=1−F−alpha<0`, `B<0`, and the literal first root is `−B≠0`, while its scale b is zero. The new graph has J>0 because its `B=b*h` constraint would give B=0, contradicting the same strict negativity at J=0. Thus b>0 for both.

The old first norm forces C>0: if C≤0 then B<0 and the signed root exceeds `b*(ell+k)`; the norm radicand is at most `(ell+k)²` because `ell*k+k²−1≥0`. For the new graph, `B=b*h≥0` and F>0 instead force C>0. In either graph, shifted F and alpha are positive, so C>0 gives `F≤q−2`. Since X=q*w>0, w≥1 and X≥q; K0≥1 then gives

```text
B=C*(X+K0)−F ≥ q+1−(q−2)=3.
```

## Both witness maps

At an old zero, `b² | Z²`, so integer square divisibility gives `b | Z`; the literal first root then gives `b | B`. Set `h=B/b≥1` and `tau=|Z|/b`. The old first norm becomes the new normalized first residual and the carrier constraint holds; the same main coordinates give A1=0.

At a new zero, B=b*h and B>0 force h≥1. The normalized first norm makes `tau>ell`. Define

```text
r = tau−ell−k + k*b*h+h.
```

It is natural because b,h≥1 imply `k*b*h≥k`. Substituting it and B=b*h into the literal first root gives **exactly** `Z=b*tau`; the old first residual is zero, and A1 is unchanged. Both maps preserve the other eight old witness coordinates. Thus the two equations have the same zero existence under the displayed port assumptions, without requiring a pointwise identity of their outputs or a fixed sign of the original Z.

## Degree and reproduction

The main residual is identical to the 9/64 graph. The carrier residual has degree at most 3 and the normalized first residual at most 22 in the ten natural witnesses, while the main residual has degree at most 30 after the [documented cancellation](../ordinary9-shifted-free-aux-two-norm64/README.md). The output degree is therefore at most 60. Its ray leading term is `64*beta^42*t^60`; the first two squared residuals have lower degree. Thus the degree is exactly 60 for fixed nonzero beta.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-two-norm-divisible61/check.py | cmp - research/ordinary10-two-norm-divisible61/receipt.json
```

The checker pins and reproduces the earlier graph receipt, verifies the exact row transformation and main expression tree, all ten inputs and 61 operations are live, the inverse-root identity as an integer polynomial, the leading ray and bounded Pell controls. The quantified divisibility, inequality and witness-map arguments are given above; the finite controls do not replace them. No Lean, build, provider/axiom audit or original-parent reverse bridge was performed.

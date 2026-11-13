# Positive J and the usual mask bounds do not recover the inverse

The 60-operation carrier candidate has an exact natural zero with `J=1` and ports satisfying `beta>0`, `K0>0`, `MC<beta`, and `MF<2*beta`, yet its reconstructed old coordinate `alpha=q-F-C` is negative. Thus simply forcing `J>0`, even together with these coarse mask inequalities, does not justify the direct inverse to the 61-operation graph. The witness works for every natural `K0`, including positive values. Its `beta=1` is **not** the actual compact beta; a stronger result for that fixed numeral is not claimed. Nor is existential inequivalence to the 61 graph established.

The parameters are `beta=1`, `MC=0`, `MF=1`, and arbitrary natural `K0`. Set `J=1`, `q=2`, `w=1`, `s=1`, `X=2`, `Y=8`, `U=32`, `F=1`, `C=9`, and `h=9*K0+17`. The literal carrier residual is zero because

```text
C*(X+K0)-F = 9*K0+17 = (beta*J)*h.
```

The rank equals `-19`, and `q-F-C=-8`. Define first Pell witnesses `(tau,k)` by 855 iterations from `(1,0)` of

```text
(tau,k) ↦ (257*tau + 33024*k, 2*tau + 257*k).
```

Define main witnesses `(g,c)` by 1351 iterations from `(1,0)` of

```text
(g,c) ↦ (26*g + 675*c, g + 26*c).
```

The finite exact computation in `check.py` verifies `8*k≤c<9*k` and `99 | 32*(g-2-24*c)`. Define

```text
eta   = c - 8*k,
zeta0 = 9*k - c - 1,
t     = 32*(g - 2 - 24*c)/99,
gamma = (t + 18 + k)/32.
```

The checker verifies that `eta`, `zeta0`, and `gamma` are nonnegative integers. The ten literal inputs are

```text
(n_J,n_F,n_C,n_w,n_s,n_h,n_tau,n_eta,n_zeta,n_gamma)
 = (1,0,8,1,0,9*K0+17,tau,eta,zeta0,gamma).
```

Both Pell equations hold by exact integer computation. The actual main root is `Dstar=32*g`; therefore the carrier, first norm and main norm residuals all vanish. The checker evaluates every candidate graph row as an exact polynomial in the symbolic natural `K0`, avoiding any expansion of an actual compact port value. The other ports are fixed as above. Its receipt states precisely what it checks.

Replacing the 60 candidate's `J` by `1+n_J` would remove its universal `J=0` counterexample, at the cost of a binary addition under the usual circuit counting convention. This example shows that even the modified graph still has natural zeros outside the image of the direct alpha-coordinate inverse under the displayed coarse bounds. A separate proof or a different witness transformation would be needed for the actual compact tuple. The original 61 equation additionally forces `J>0` when `K0>0`, but that fact does not supply the missing inverse bound for the modified 60 graph.

Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-carrier60-positive-j-mask-bounds-counterexample/check.py | cmp - research/ordinary10-carrier60-positive-j-mask-bounds-counterexample/receipt.json
```

This is a standard-integer source-level certificate. No Lean, build, model, provider, original-parent, Con(ZFC), or iPRA claim is made.

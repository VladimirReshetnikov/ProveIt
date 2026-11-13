# A positive-J boundary zero with reconstructed alpha exactly zero

Even requiring `J>0`, `beta>0`, `MC<beta`, `MF<2*beta` and the **non-strict** bound `q-F-C≥0` does not make the 60-operation candidate's direct inverse to the 61 graph valid: the latter requires strict positivity. For `beta=1`, `MC=0`, `MF=1`, and arbitrary natural `K0`, an exact full 60-graph zero has `J=1`, `q=2`, `F=C=1`, hence reconstructed `alpha=0`. This is not the fixed compact beta, and it does not establish an existential inequivalence or rule out another witness map.

Let `(tau,k)` be the 8659th iterate from `(1,0)` of `(tau,k) ↦ (257*tau+33024*k, 2*tau+257*k)`, and `(g,c)` the 13681st iterate from `(1,0)` of `(g,c) ↦ (26*g+675*c, g+26*c)`. Exact finite arithmetic verifies `8*k≤c<9*k`, `99 | 32*(g-2-24*c)`, and that the following gamma is a natural integer:

```text
eta = c-8*k,  zeta0 = 9*k-c-1,
t = 32*(g-2-24*c)/99,  gamma = (t-6+k)/32.
```

The ten candidate inputs in their literal order are

```text
(1, 0, 0, 1, 0, K0+1, tau, eta, zeta0, gamma).
```

Here `X=2`, `Y=8`, `U=32`, the rank is 5, and the signed main root is `32*g`. The carrier residual, first Pell residual and main Pell residual all vanish. The checker pins the literal JSON and evaluates every row exactly over the polynomial ring `Z[K0]`, verifies every input is natural for natural `K0`, and checks both full Pell identities and the alpha boundary. It prints no enormous Pell integers.

Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-carrier60-positive-j-alpha-zero-mask-counterexample/check.py | cmp - research/ordinary10-carrier60-positive-j-alpha-zero-mask-counterexample/receipt.json
```

This is a standard-integer source calculation, not a Lean, nonstandard-model, original-parent, Con(ZFC), or iPRA proof.

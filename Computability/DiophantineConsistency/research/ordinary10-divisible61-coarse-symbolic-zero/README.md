# A noncompact symbolic zero of the 10/61 graph

Projecting the pinned [coarse-port first/main Pell witness](../ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero/README.md) through the [10/61 witness map](../ordinary10-two-norm-divisible61/README.md) gives a standard-natural zero of the 10/61 equation at ports `(127,87,54,139)`. These are not the fixed symbolic compact tuple. This does not establish a zero of the original shifted 85-parent, a fixed-port counterexample, or an iPRA result.

Use the pinned construction's `L=2172`, `n=L(2L+1)=9,437,340`, `m=n+L=9,439,512`, `q=128`, `X=2^m`, `Y=2^L`, and `M=XY²`. Let `(tau,yFirst)` be the nth Pell pair with multiplier `2M+1`, `k=2*yFirst`; let `(g,c)` be the mth pair with multiplier `a+2`, where `a=Y*(X+1)`. Put `eta=c−Yk`, and let gamma be the nonnegative main-root quotient specified in the pinned source. That source proves `0<eta<k` and the first/main signed-norm equations. Its actual rank is `R=18,874,679=2n−1`.

Here beta=127, F=119, alpha=8 and C=1, so the literal first carrier is `B=X+87−119=X−32`. Since m≡5 mod 7, `X≡32 mod 127`; hence `h=(X−32)/127` is a positive integer. The complete 10/61 input, in its listed order, is

```text
(1, 118, 7, 2^(m−7), 2^(L−21)−1,
 h, tau, eta, k−eta−1, gamma).
```

The `−1` in the zeta input restores this graph's shifted-zeta convention. The first carrier residual is zero, the normalized tau residual is zero by its Pell norm, and the unchanged main residual is zero by the pinned construction. Thus the sum of their squares is zero. The enormous witness is specified symbolically; it is not materialized or written to disk.

The checker pins and reproduces both earlier receipts, verifies the finite q/rank and divisibility arithmetic, and separately projects the prior smaller q=4 toy to the 10/61 graph and evaluates all 61 rows exactly. That finite toy is only a control for the symbolic argument. No Lean, build, provider, parent-zero, fixed-compact, or equivalence-to-Con(ZFC) result is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-divisible61-coarse-symbolic-zero/check.py | cmp - research/ordinary10-divisible61-coarse-symbolic-zero/receipt.json
```

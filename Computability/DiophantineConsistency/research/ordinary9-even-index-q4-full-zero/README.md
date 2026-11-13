# An exact noncompact even-index two-norm zero

The existing small `q=4` control in the [10/61 coarse-port packet](../ordinary10-divisible61-coarse-symbolic-zero/README.md) is a full even-main-index example. At the noncompact ports

```text
(beta,K0,MC,MF) = (3,1,1,1),
```

it gives natural zeros of both the **literal 9-variable/64-operation two-norm graph** and the 10-variable/61-operation divisibility graph. Its actual main Pell index is `m=84`. Every row of both graphs is evaluated exactly by this packet's checker.

The separately [reviewed even-index theorem](../../reviews/ordinary13-parent-even-index-unconditional-independent/README.md) therefore rules out completing these **same first/main data** to a zero of the shifted 85-row parent by choosing its auxiliary witnesses. This does not rule out an unrelated parent witness at these ports, prove existential inequivalence, concern the fixed compact tuple, or establish a Lean/iPRA or Con(ZFC) result.

## Exact finite witness

Let `Pell(A,j)` start at `(1,0)` and apply `(x,y) ↦ (A*x+(A²−1)*y, x+A*y)` j times. Define

```text
q = 4, L = 6, n = 78, m = 84,
X = 2^84, Y = 2^6, U = Y*q²,
M = X*Y², a = Y*(X+1), H = 4*a+3,
(tau,yFirst) = Pell(2*M+1,78), k = 2*yFirst,
(g,c) = Pell(a+2,84), eta = c-Y*k,
R = 155,
B = 2*(X+1)-1, h = B/3,
gamma = (g-X-a*c)/H + (k-R-1)/U,
ell = M*k,
r = tau-ell-k+(3*k+1)*h.
```

All indicated divisions are exact and all resulting witness coordinates are natural; the checker verifies those facts directly, including `0≤eta<k`. The rank is the literal graph value `R=(1+(q-1)*3)*(q²-1)+1+q=155`. The checker verifies `tau²=1+M*(M+1)*k²`, `g²=1+((a+2)²-1)*c²`, and the actual signed graph roots `Z=3*tau` and `Dstar=U*g`.

The nine natural graph inputs, in literal JSON order, are

```text
(1, 0, 0, X/q, 0, r, eta, k-eta-1, gamma).
```

For the ten-variable graph replace `r` by `h,tau` in the corresponding literal slots:

```text
(1, 0, 0, X/q, 0, h, tau, eta, k-eta-1, gamma).
```

The first tuple makes the 9-graph's `A0` and `A1` zero; the second makes the 10-graph's carrier, normalized first norm and `A1` zero. The actual main ordinate is exactly `y_84(a+2)`, so the main index used by the same-data obstruction is positive and even. These are finite explicit integers, not a bounded-search conjecture; their largest listed witness is under 8,000 bits. Hashes and bit sizes in the receipt identify selected computed integers without printing large decimal numerals.

The checker evaluates all 64 and 61 literal rows, respectively, and checks naturalness, the two Pell identities, divisibility, roots and graph outputs. Its arithmetic is capped at 192 MiB address space, 10 seconds CPU and zero core-file size; the reproduction command also limits wall time to 15 seconds. These checks do not constitute a Lean proof or a proof that no different parent data can work.

From `Computability/DiophantineConsistency`:

```sh
timeout 15s python3 -I -S -B research/ordinary9-even-index-q4-full-zero/check.py | cmp - research/ordinary9-even-index-q4-full-zero/receipt.json
```

No Lean, build, staging, compact-port zero or full parent inequivalence was produced.

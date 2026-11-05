# No strong-and-auxiliary completion for one q²-scale main tuple

For the exact partial tuple in the [q²-scale packet](../p64-qcube75-q2-partial-obstruction/README.md), **no positive choices of `f,i,T,y` satisfy both the original strong norm `W=0` and auxiliary unit `Na=1`**. This rules out completing that particular first/main/transport assignment. It does not rule out other first/main tuples, a zero at the same ports with other coordinates, or existence equivalence of the q²- and q³-scale graphs. It is an external proof, not a Lean theorem.

The [finite checker](check.py) verifies the arithmetic inputs used below:

```
n = 12386
D = n²−1 = 153412995 = 3 · 5 · 2477 · 4129  (distinct primes)
(g,c) = (n,1)^322_D
c is positive and even;  gcd(c,D)=1;  g²−D c²=1.
```

The corresponding first/main/transport assignment and actual natural ports are specified exactly in the linked packet. The proof below does not use their rank `R`; only the displayed `n,D,c` matter.

## 1. Consequences of the strong norm

Suppose positive `f,i,T,y` satisfy `W=0` and `Na=1`. Put `I=i c²`. Then `I>0` is even and

```
I² = D (f²−1).                                  (1)
```

Since `D` is squarefree, `D | I`; write `I=D L` with `L>0`. Equation (1) gives

```
f² − D L² = 1.                                  (2)
```

Since `gcd(D,c)=1` and `c² | I`, also `c² | L`. Equation (2) makes `f>1` and `f²≡1 (mod c⁴)`, hence `gcd(f,c)=1`. Equation (1), with even `I` and odd `D`, shows that `f` is odd. Choose any prime `p | f`. It is odd; (2) shows `p∤D`, and `gcd(f,c)=1` shows `p∤c`.

Write `α=n+√D`. Every positive solution of (2) is a positive power of `α`, because `D=n²−1`: from a positive solution `(x,y)` the transformation

```
(x,y) ↦ (n x−D y, n y−x)
```

preserves the norm, has positive first coordinate and a nonnegative second coordinate strictly smaller than `y`, and reaches `(1,0)`. Thus `f+L√D=α^N` for some `N>0`.

Work in a finite field containing `√D` over `F_p` (one can use `F_{p²}`); `√D` is nonzero. Since `f≡0` and (2) gives `D L²≡−1`,

```
α^N = L√D,      α^(2N) = −1.
```

Consequently the multiplicative order `o` of `α` is divisible by 4: an even exponent gives the element of order 2. In particular `−1=α^(o/2)` and `o/2` is even.

## 2. Consequences of the auxiliary unit

The graph's `V` is `f²(cT−R)−c`, so `p | f` implies

```
V ≡ −c  (mod p).                                (3)
```

Using (1), the unit `Na=1` becomes

```
(I V)² − (I²−1)y² = 1.                           (4)
```

Here `I≥2`. The same descent applied to `I²−1` shows that, for some `j>0`,

```
I|V| + y√(I²−1) = (I+√(I²−1))^j.
```

Let `T_j` be the usual Chebyshev polynomial of the first kind. Since the real coefficient `T_j(I)` is divisible by `I`, `j` is odd: the recurrence `T_{j+1}(I)=2I T_j(I)−T_{j−1}(I)` gives `T_j(I)≡±1 (mod I)` for even `j`. Equation (1) and `p|f` give `I²≡−D=1−n² (mod p)`; also `p∤I`. For odd `j`, the Chebyshev recurrences therefore yield

```
T_j(I)/I ≡ (−1)^((j−1)/2) U_(j−1)(n)  (mod p),   (5)
```

where `U` is the second-kind Chebyshev polynomial. To check (5), the sequences indexed by `r=(j−1)/2` both start with 1, their next values agree by `I²≡1−n²`, and their two-step recurrences agree after the indicated alternating sign. The sign of `V` is arbitrary, so (3)–(5) imply

```
U_(j−1)(n) ≡ ±c  (mod p),   with j odd.           (6)
```

But the exact main definition is `c=U_321(n)`, with **even** index 322. For every positive `k`,

```
α^k − α^(−k) = 2√D U_(k−1)(n).
```

Because `2√D` is nonzero in the field, (6) implies

```
α^j ∈ { α^322, −α^322, α^(−322), −α^(−322) }.
```

The exponents corresponding to all four possibilities are even modulo `o`: both 322 and `o/2` are even. Since `o` is even, an odd `j` cannot be congruent to any of them. This is the contradiction.

In particular, the [modulo-223 obstruction](../p64-qcube75-q2-strong-choice-obstruction/README.md) for one selected symbolic strong witness is a special case; varying its exponent to `c*h` cannot produce an auxiliary completion. The proof above covers all positive `f,i`, not just that family. The script verifies its finite numerical hypotheses; it does not verify the universal mathematical argument or invoke Lean.

Run from any directory:

```
python3 -I -S -B path/to/p64-qcube75-q2-all-strong-obstruction/check.py
```

The deterministic result and script hash are frozen in `result.json`.

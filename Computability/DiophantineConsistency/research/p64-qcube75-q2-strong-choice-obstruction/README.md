# Auxiliary obstruction for one symbolic strong witness

This concerns the exact first/main/transport partial tuple in the [q²-scale packet](../p64-qcube75-q2-partial-obstruction/README.md), in which `D=12386²−1`, `(g,c)=(12386,1)^322_D`, and the strong-norm witness is specified by

```
(f,L) = (g,c)^c_D;    I = D L;    i = I/c².
```

For **this particular** `f,i`, no integers `T,y` with `y>0` can satisfy the auxiliary unit equation `Na=1`. Therefore this choice cannot complete that partial tuple to a graph zero. This says nothing about another strong witness, another partial tuple, the fixed compact44 ports, or existence equivalence of either graph.

The script uses exact binary exponentiation modulo 223 with the actual 4686-bit exponent `c` and checks

```
c ≡ 19,  D ≡ 145,  f ≡ 0,  L ≡ 42,  I ≡ 69   (mod 223).
```

The auxiliary graph expression is `V=f²(cT−R)−c`, so **every** `T` would give `V≡−c≡204 (mod 223)`. The original strong identity `I²=D(f²−1)` and `Na=1` instead give

```
(I V)² − (I²−1)y² = 1.                         (∗)
```

## Pell descent and the finite test

The symbolic construction has `I≥2`. For any solution of (∗) with `y>0`, put `x=I|V|`; then `x>0`. Let `h=I²−1` and define

```
x' = I x − h y,       y' = I y − x.
```

The norm equation is preserved. Since `x²=h y²+1≤I²y²`, `y'≥0`; since `x>(I−1)y`, `y'<y`; and `x'>0` follows from `x>√h y`. Descent ends at `(1,0)`, so every such `(x,y)` is a positive power of `I+√h`.

For the real coefficients `a_j` of those powers, `a_0=1`, `a_1=I`, and `a_{j+1}=2I a_j−a_{j−1}`. Modulo `I`, every even-indexed `a_j` is `±1`, so `I | x` forces the exponent `j` to be odd. As `I≡69` is invertible modulo 223, `|V|≡a_j / 69 (mod 223)`. The script computes the recurrence modulo 223 together with index parity, verifies return to its initial state after 32 steps, and checks that its odd-indexed quotients are exactly

```
{1, 47, 86, 101, 122, 137, 176, 222}.
```

This set is closed under negation, so it also covers negative `V`. It does not contain 204. Thus the asserted auxiliary completion is impossible. The check does not construct or expand the enormous `f,L,I`, and its proof relies on the elementary descent above in addition to the finite residue computation; it is not a Lean theorem.

Run from any directory:

```
python3 -I -S -B path/to/p64-qcube75-q2-strong-choice-obstruction/check.py
```

The output is frozen in `result.json`, with the checker hash.

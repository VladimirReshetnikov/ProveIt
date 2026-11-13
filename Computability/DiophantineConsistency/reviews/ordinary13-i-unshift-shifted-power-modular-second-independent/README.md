# Independent review: fixed-port shifted-power modular obstructions

The reviewed `research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/` correctly separates two special witness families. Its modular exclusions do not show that the fixed-port i-unshift graph has no zero, or that any other witness or shifted rank relation is impossible.

For the general leading-power comparison, let `X=2^m`, `Y=2^L`, `m=n+d`, `P=2XY`, and `Q=4XY²`. The independent checker expands the difference of the two binary exponents and verifies the polynomial identity

```text
(m−1)*(m+L+1) − (1+L+(n−1)*(m+2L+2))
 = d*(d+L+1)−n*(L+1−d).
```

Thus equality `P^(m−1)=2Y*Q^(n−1)` is equivalent to the displayed matching equation. For `d=L−1`, this gives `n=L(L−1)` and `m=L²−1`. The lower and upper Pell ordinate bounds in the pinned coarse-bounds construction give `0<eta=c−Yk<k` under the stated `4(m−1)Y<X` condition. For L≥4, the latter follows from `4(L²−2)<2^(L²−L−1)`: it holds at 4 and the right side's exponent increases by 2L at each successor while the quadratic left side grows by less than a factor 4. These interval observations do not imply the required actual-rank equality.

Independent Horner evaluation of the source-defined compact low and high digits gives `beta≡MC≡MF≡1 mod 3`. For **any natural J with q=1+beta*J a power of 2**, q≡±1 and the graph rank satisfies `R≡J(1+q)≡q²−1≡0 mod 3`. But `2L(2L+1)−1` has residues 2, 2, 1. This rules out the first matched rank for that scope. No conclusion for q divisible by 3 follows from this argument.

The independent checker proves primality of 193707721 by trial division through 13917, verifies `2^67≡1`, and recomputes the fixed source digit residues modulo the prime. For J=1 it gets `R≡55801659`. If `R=2L(L−1)−1`, then `(4L−2)²≡8R+12≡58997842`. Euler's criterion gives residue p−1, so the required square does not exist.

The second test is genuinely J-specific. For instance, `J₀=113487015` satisfies `J₀*(MC+MF)≡−1 mod p`, making the required square residue 4 rather than a nonsquare. Even with q restricted to powers of two, this residue is possible: letting `q=(2^N)^J₀`, `beta=2^N−1` and `J=(q−1)/beta`, the geometric sum gives `J≡J₀ mod p`, because `2^N≡1 mod p`. This is only a modular non-obstruction; it does not provide a graph witness.

The checker pins the relevant source recipes and graph, reproduces the author's receipt, performs a second direct digit Horner calculation, separately checks primality and Euler's criterion, and proves the exponent relation by exact sparse-polynomial expansion. It uses finite controls for the elementary inequality; the induction is described above. No Lean, build, staging, fixed compact graph-zero decision or iPRA conclusion was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-i-unshift-shifted-power-modular-second-independent/check.py | cmp - reviews/ordinary13-i-unshift-shifted-power-modular-second-independent/receipt.json
```

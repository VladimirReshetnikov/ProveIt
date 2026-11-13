# Independent review of the minimal kernel-complement example

The fact-level example and its claimed scope check out: `(A,m)=(3,2)` is lexicographically first outside the kernel-gcd criterion, and the least strong witness has `f=19601`, `I=55440`, `i=1540`. No concrete error was found in the proof excluding all same-data auxiliary witnesses. The example cannot satisfy the actual graph's signed main norm, so it is not a graph zero or an existential separation.

For `A=2`, `Delta=3` is squarefree, making `gcd(c²,3)` divide every positive c. The next multiplier `A=3` has `Delta=8=2*2²`, and its first positive even index is `m=2`, where `(x_m,c)=(17,6)` and `gcd(36,4)=4` does not divide 6. Thus the lexicographic claim concerns these fact-level pairs, not the size of a full graph solution.

The actual strong equation with `I=36i>0` implies `4 | I`; putting `u=I/4` gives `f²-2u²=1`. The least positive integer-coordinate norm-one unit is `3+2*sqrt(2)`, so ordinary Pell classification gives `f=x_h(3)` and `I=8*y_h(3)` for some h>0. The first six ordinates modulo 9 are `1,6,8,6,1,0`; since `36 | I` is equivalent to `9 | y_h(3)` and x increases, h=6 gives the least positive witness. The checker separately tests every smaller integer f by exact square roots; it does not substitute for the general Pell classification.

For every h, `x_h(3)` is odd and greater than one, so an odd prime p divides it. The norm makes `Q^h` an invertible anti-diagonal matrix modulo p. If an odd-index ordinate vanished, its transition would be `±Id`; its hth power would be diagonal, whereas the odd power of the anti-diagonal `Q^h` is anti-diagonal. Thus no odd ordinate vanishes mod p, regardless of the parity of h. The Pell addition identity excludes both `y_ell≡c` and `y_ell≡-c` for odd ell. Standard classification of the auxiliary norm, together with the exact quotient polynomial and `V≡-c mod f²`, shows that either sign of any auxiliary root would force one of those excluded congruences. This is a universal same-data argument, not merely the finite `p=17` check for the smallest f.

In the literal graph `A=Y*(X+1)+2`, with `Y=q³s`, `q≥1`, `s≥1` and `X≥0`. Therefore `A=3` forces `Y=1`, `X=0`, `q=s=1`, `a=1`, `H=7` and `U=1`. The actual main-root row then gives `d≡c mod 7`, while the main norm requires `d²-8c²=1`. Modulo 7 these are incompatible. This directly explains why the fact-level Pell pair cannot be an actual graph main solution.

The independent checker pins the reviewed packet, prior obstruction and graph, verifies the literal main-root operands, tests the least witness both by recurrence and exhaustive smaller f, checks the four-step quotient cycle modulo 17, and traverses complete bounded modular parity cycles. These checks corroborate the ordinary-integer argument; they do not prove a Lean theorem, a model transfer, a full graph zero or provider provenance.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-even-index-kernel-complement-minimal-independent/check.py | cmp - reviews/ordinary13-even-index-kernel-complement-minimal-independent/receipt.json
```

No Lean, build or staging was run.

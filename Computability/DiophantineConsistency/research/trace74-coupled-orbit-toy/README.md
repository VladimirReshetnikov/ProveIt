# Abstract coupled Pell-orbit diagnostic

This is an exact finite **abstract toy**, not a trace74 graph zero or a
Lean theorem. It independently checks the positive-`V` congruence branch
needed by a proposed construction of the coupled output equation.

Take the main Pell unit `lambda+sqrt(delta)` with `lambda=2`, `delta=3`,
odd main index `r=5`, ordinate `c=209`, and `tau=1`. The toy chooses
`u=r*c=1045` and verifies by exact unit exponentiation that `c²*tau`
divides the `u`th ordinate. Put `froot=x_u`, `U=y_u/tau`,
`a=delta*U²*tau²`, `F=1+2a=x_(2u)`, `I=y_(2u)`, and `S=delta*I`.
The check verifies `F²−delta*I²=1`, `c²|I`, `c|2u`, `F≡1 (mod c)`,
`gcd(F,c)=1`, and

```text
Q=delta*4a(1+a)=S².
```

Set `j=2u`, odd auxiliary index `s=r+2j`, and `h=(s−1)/2=2092`.
The checker evaluates the positive auxiliary quotient `V_h=T_s(S)/S`
**only modulo `F*c`**, using a separate modular 2×2 recurrence, and verifies

```text
V_h ≡ −c (mod F),      V_h ≡ r (mod c).
```

Thus for the toy signed rank `R=−r`, the numerator
`V_h+c+F*R` is divisible by `F*c`. It does not construct or check the
resulting positive `T`, any carrier coordinate or the graph output.

The congruences have an ordinary-integer algebraic explanation. The
Chebyshev identity
`T_(2h+1)(S)/S ≡ (−1)^h U_(2h)(lambda) (mod F)` follows by recurrence
from `S²+lambda²≡1 (mod F)`. Since `x_j=F`, Pell composition gives
`y_(r+2j)≡−y_r=−c (mod F)`. Since `c|S` and `c|j`, the auxiliary
recurrence also gives `V_h≡(−1)^h(2h+1)≡r (mod c)` for even `h`.
The same congruence pattern can be used in a larger construction only
after checking its own index, modulus and sign hypotheses.

Run from the repository root:

```text
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-coupled-orbit-toy/check.py
```

It exited 0 and printed `abstract toy: r=5, c=209, u=1045, j=2090,
h=2092; congruences PASS`. This finite diagnostic is not a proof of the
symbolic fixed-beta case, full graph-zero existence, or any iPRA claim.

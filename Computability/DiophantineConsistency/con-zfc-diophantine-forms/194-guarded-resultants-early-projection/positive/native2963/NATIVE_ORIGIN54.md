# The forced Start digit in compact54

`NativeLowPort54` defines the complete low-mask arithmetic recipe from the
assignment positions of `NativeStencil54.entries`, omitting the forbidden
selector at position 1:

```
rho = 2^89, L = 4831,
removed = sum_(e in E, e!=1) rho^e + 2*rho^507,
MC_recipe = rho^L − 1 − removed.
```

The sum is a literal finite list extracted from the frozen entry table.
Lean checks its length 519, leading position zero and positive remaining
positions. It proves `removed <= 521*rho^1807`, justifies both natural
subtractions, and proves

```
MC_recipe + removed + 1 = rho^L,
MC_recipe % rho = rho−2.
```

The proof keeps the large integer symbolic. The fixed tuple's byte-to-recipe
binding is a separate finite obligation; it is not inferred from its height.

`NativeSourceOrigin54` uses the already proved native source mask equation.
For the existing arithmetic coefficient interface, `d>=89`, and the low-port
binding `MC=MC_recipe`, it derives

```
J % rho = 1,
(MC*J+1) % rho = rho−1,
(C−1) % rho = 0,
C % rho = 1.
```

The decrement is justified by the proved source bound `C>0`. Consequently,
every reconstructed radix digit array `c`, with `word(rho,c)=C` and
`c[i]<=3` as in `NativeWindowConvolution54`, satisfies `c[0]=1`.
This fixes the whole origin digit, hence the Start-selector input, without
assuming an occupied cell or temporal phase alignment.

The two modules and their dedicated checks pass. All 12 public theorems use
only `propext`, `Classical.choice` and `Quot.sound`. The low-port build emits
three notices that large symbolic exponentiations were intentionally not
evaluated; they are not failed proof obligations.

Full sparse-digit reconstruction and the literal basis/clean-band argument
remain open. These lemmas do not assert the native-machine calibration, its
reverse witness construction, or the encoded ZFC consistency biconditional.

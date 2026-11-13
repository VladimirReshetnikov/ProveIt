# Independent source review: conditional sign-free power recovery

The lower-bound client needs only `q>=46`, X>0 and `q | 3X`: the positive product gives `q<=3X`, hence X>=16. It does not cancel 3 or infer `q | X`. The growth client separately assumes the first Pell ordinate at n, the main ordinate at R, `2n=R+1`, n>=13, the c/k definitions and zeta>0. Its substitution `r=n-1` gives r>=2 and `R=2r+1`, matching the pinned `ArithmeticPellPowerRecovery.power_bound` interface. The currently cited graph exact-index client does not itself export both recurrence-coordinate equalities.

The power projection assumes the stronger oriented q-balance and **both** main coordinates at the same R, plus `Y=q³s` and the growth bound `2^R<Y`. With `H=3+q*d`, the draft's additive three-times-balance identity follows from that balance and the H identity; its sign and all terms were independently verified in a free polynomial ring. The projection quotient then gives the same main root as `2^R+a*c+H*w`. Reducing modulo H and cancelling the shared additive `3*a*c` gives `3X≡3*2^R (mod H)`. Both sides lie strictly below H, since X<a and `2^R<Y<=a`; equality and cancellation of nonzero 3 give `X=2^R`, without a Bézout or q-divides-X premise.

The stronger balance and its natural witness W, both exact graph recurrence coordinates, compact model bound q>=46, eta-zero applicability, later R/X bounds and all graph/provider/port bindings remain explicit external inputs. The checker's finite controls and free-ring algebra do not elaborate the Lean tactics or establish an internal iPRA endpoint. The author's receipt reproduces; no Lean was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-signfree-power-independent/check.py | cmp - reviews/ordinary13-residue-signfree-power-independent/result.json
python3 -I -S -B research/ordinary13-residue-signfree-power-model-draft/check.py | cmp - research/ordinary13-residue-signfree-power-model-draft/receipt.json
```

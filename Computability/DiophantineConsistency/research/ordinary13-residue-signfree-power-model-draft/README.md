# Conditional sign-free power recovery in an IΣ₁ model

This is an **unelaborated source draft**, not a checked theorem or an iPRA
endpoint. It isolates the extra facts beyond the separate `q ∣ 3X` draft.
All variables below are model naturals and exponentiation is represented in
the existing IΣ₁ model interface.

* `sixteen_of_three_projection` uses `46 ≤ q`, `0 < X` and `q ∣ 3X`.
  Since `3X > 0`, divisibility gives `q ≤ 3X`, hence `16 ≤ X`.
  It does not assert `q ∣ X` or any coprimality. The compact condition
  `46 ≤ beta` together with positive J gives `q=1+J*beta ≥ 47`, **provided**
  that the appropriate model-port cast and compact bound are supplied.
* `growth_of_coordinates` calls `power_bound` with the exact premises
  `13 ≤ n`, `2n=R+1`, `c=kY+eta`, `k=eta+zeta`, `zeta>0`,
  `c=ycoord R (Y*(X+1))`, and
  `k=2*ycoord n (2*(X*Y²-1)+1)`. It gets `2^R<Y` after setting
  `r=n-1`. The current graph exact-index result returns n and index
  equalities, but **does not export** either recurrence-coordinate equality;
  these must be transported with their actual witnesses from the upstream
  graph and classification proofs, without substituting a different root.
* `power_of_oriented_balance` assumes the natural main root is exactly
  `xcoord R (Y*(X+1))` and the ordinate is the matching `ycoord`; it also
  assumes the explicit graph balance
  `q*(main+H*W)=q*(X+a*c+H*gamma)+H*X`, with `a=Y*(X+1)`, `H=3+4a`,
  and `Y=q³s`. It uses the existing Pell `projection_quotient` and
  reduces 3 times the balance modulo H. The strict ranges `3X<H` and
  `3*2^R<H` then give `X=2^R`. This does not assume a Bézout identity or
  `q ∣ X`.

The balance is stronger than `q ∣ 3X`. A proposed graph binding can set
`W=4*X*q*s*w`: from the previously drafted exact index
`k=R+1+4*(X*Y²)*w` and the residue-adjusted actual-root balance, use
`U=Y*q²` and cancel the strictly positive `Y*q`. That conversion and
its actual witness are **not proved by this packet**. It also does not
establish `R≥q³`, `X≥q²`, fixed compact port bounds, any eta-zero case,
provider compatibility, or any internal iPRA equivalence.

Run `python3 -I -S -B research/ordinary13-residue-signfree-power-model-draft/check.py`
from `Computability/DiophantineConsistency`. The deterministic check pins
source files and tests finite arithmetic and polynomial rearrangements;
it does not execute Lean or validate tactic elaboration or theorems.

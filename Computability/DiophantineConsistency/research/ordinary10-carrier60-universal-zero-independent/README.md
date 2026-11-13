# The 60-operation carrier candidate has a zero for every natural port tuple

The 60-operation carrier candidate in `research/ordinary10-carrier60-inverse-boundary/candidate.json` is **solvable for every choice of its four nonnegative fixed numerals**, including the actual compact tuple. This strengthens the earlier positive-port counterexample to the direct inverse: the candidate cannot express nonexistence at the compact ports. The original 61-operation equation and its existence status are not determined here, and no parent-equation, consistency or iPRA equivalence is asserted.

For any natural `beta`, `K0`, `MC`, `MF`, assign the ten natural witness inputs in the exact order of the candidate as follows:

```text
n_J     = 0          n_F    = K0       n_C   = 0
n_w     = 1          n_s    = 0        n_h   = 0
n_tau   = 3363       n_eta  = 1527     n_zeta = 850
n_gamma = 292
```

All inputs are natural even when `K0=0`. The resulting values include

```text
q = X = Y = U = C = 1,  F = K0 + 1,  R = 0,
a = 2, H = 11, Delta = 15, k = 2378, c = 3905,
ell = 2378, Dstar = -15124.
```

In particular the carrier residual is `1*(1+K0)-(K0+1)-0=0`. The first and main norm residuals vanish by the exact integer identities

```text
3363²  = 1 + 2*2378²,
15124² = 1 + 15*3905².
```

The graph uses integer subtraction in its intermediate nodes, so its negative `Dstar` is permitted. The three squared residuals and the final output are exactly zero. Its old-coordinate reconstruction has `q-F-C = -K0-1`, which is never positive for natural `K0`; thus the former coordinate inverse fails here even at the fixed compact tuple. This is a full literal zero, but it does **not** rule out a different, non-coordinate witness map or prove an existential inequivalence with the 61-operation graph. In particular, universal solvability of this candidate alone is not a proof that the 61-operation graph has no solution.

The failed branch is structurally significant: in the 61 graph, `J=0` gives `q=1` and `C=1-F-alpha≤-1`. With `K0>0`, its carrier residual `C*(X+K0)-F` is strictly negative, so a 61 zero must have `J>0`. The 60 graph instead permits an independent positive `C`; at `J=0`, choosing `C=1` and `F=X+K0` satisfies that carrier. Forcing `J>0` would exclude the displayed witness but does not by itself prove the missing reconstructed-alpha bound.

`check.py` reads the pinned literal JSON and evaluates **all 60 rows over the polynomial ring in the four symbolic port variables**, using a small exact sparse integer-polynomial implementation; it checks the complete output is the zero polynomial and checks every asserted intermediate. It also checks literal topology, liveness, witness order, both numerical Pell identities and the negative reconstructed alpha. The arithmetic verification avoids expanding the huge compact numerals; the result applies to them because they are natural fixed numerals. It does not independently establish the original compact port recipes, prove anything about nonstandard models, or provide a Lean/provider/axiom audit.

From `Computability/DiophantineConsistency`, reproduce with:

```sh
python3 -I -S -B research/ordinary10-carrier60-universal-zero-independent/check.py | cmp - research/ordinary10-carrier60-universal-zero-independent/receipt.json
```

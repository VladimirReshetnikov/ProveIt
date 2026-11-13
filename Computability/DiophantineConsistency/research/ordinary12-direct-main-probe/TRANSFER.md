# Conditional transfer of the direct balance

`DirectMainTransfer.lean` proves, in any commutative semiring, that

`U*(X+a*c)+H*(U*G+R+1) = H*k+U*main`

implies

`H*(U*w+R+1)+U*(X+a*c+H*G) = H*k+U*(main+H*w)`.

A second ring identity proves `((q*w)*(q³*s))*q = (q⁵*s)*w`. These are exactly stated algebraic lemmas, not an application to a graph or to `FreeJMainCongruence`. In particular the adjusted witness is a congruence witness and is not asserted to be the Pell root. Constructing the old valuation and proving the actual graph hypotheses and positivity remain open, as described in [ROUTE.md](ROUTE.md).

`run-transfer.py` produced `observations/transfer-attempt01/terminal.json` and source and stdout/stderr snapshots. Lean exited 0 without warnings; each theorem's printed axiom report lists only `propext`. Source SHA-256 is `2308aa52cbb8e05c412f96f511805cb9f759ef9dcefb2665b6c061544d29e055`, imported projection object SHA-256 is `e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182`, and resulting object SHA-256 is `f6c24060e4a91ad3710bab840133e4c70987c55f3e95246a5d4452de48852f78`. The selected 1,291-object union was unchanged. The receipt records overlap with one other Lean process and resource samples. Package, dynamic, and source-to-object ancestry are inherited, not freshly rebuilt, and temporary paths may disappear.

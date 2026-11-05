# Independent review of fixed-mask gcd partial assignments

**PASS for the stated partial-assignment scope.** The independent `check.py`
pins the graph and the current source definitions of the fixed radix and
masks, reconstructs the actual `beta`, low mask and high mask from their
finite base-`2^67` digit recipes, verifies their bounds, and computes the
actual transport and quartic rank inequalities for all three assignments.
It independently checks the three residues modulo 9 and reruns the author's
132 analogous small-graph controls, matching the retained result. This is an
external integer check; it does not authenticate the complete Lean provider
ancestry or run Lean.

The fixed tuple uses `beta=2^590069−1`, `MC=lowNat`,
`MF=beta+highNat`; `K=q−w` varies with the assignment. The pinned low-mask
source gives the weighted support subtraction, and the high-mask source
gives the explicit 8,807 base digits. Their reconstruction establishes
`0≤MC<beta` and `0<MF<2beta`. With `F=1`, `alpha=q−2`, `z=1`, the transport
gap is 1 and both sides of the transport equation equal `q`.

Since `beta≡4 (mod 9)`, the rows `(J,s,w)=(1,1,1),(2,1,1),(1,3,3)`
give `(Y,H) mod 9=(8,6),(0,3),(6,0)`. Every common divisor of `Y²` and
`H=3+4(X+1)Y` divides 9, because `H≡4(X+1)Y+3` and `e|Y²,e|H` imply
`e|9`. These residues therefore give the exact gcds 1, 3 and 9. Putting
`h=Y²/e` and `g=X+ac+H/e` proves the displayed free-carrier identity;
for `e>1`, `0<h<Y²`, so `Y²` does not divide `h`.

The fixed mask bounds give `(MC+q*MF)J<(q−1)(1+2q)` and hence
`R+1<q⁴−q³+1<q⁴`. The constructed positive assignments are **not zeros**:
`eta=zeta=t=1` makes `A0=1−(2P)(2P+2)≤−7`, so `A0*Na−1` is nonzero for
every integer `Na` and the output sum of squares is positive. In particular
the separate main Pell, strong and auxiliary residuals are not imposed.
These examples do not show that an actual fixed-port zero has `e>1` or
`Y²∤h`, nor do they settle reverse existence or an iPRA endpoint.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-mask-gcd-independent/check.py
```

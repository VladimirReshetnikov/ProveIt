# Independent review of the standard-integer carrier criterion

**PASS under the packet's explicit standard-integer assumptions.** Let
`Y=q³s`, `U=Y²`, `H=4(XY+Y)+3`, `e=gcd(U,H)`, `mu=U/e`, and
`d=2n−R−1`. Assume `q≥3`, `s,X,h>0`, the displayed free-carrier equation,
`n<R<2n`, `R+1<q⁴`, and `k=2n+4XUλ` for some nonnegative integer `λ`.
Then a positive natural `gamma` with `U*gamma=h+k−R−1` exists **if and only
if** `d=0` and `U|h`.

The proof checks in both directions. Since `e|Y²` and `e|H`, reducing
`H²=(3+4(X+1)Y)²` modulo `e` gives `e|9`, and the carrier gives `mu|h`
by gcd cancellation. Thus `mu≥q⁶/9≥q⁴>R+1`. The integer window implies
`0≤d≤R−3<mu`. If the old carrier quotient exists, `U|(h+d)`; together with
`mu|h` and `mu|U`, this gives `mu|d`, hence `d=0`, then `U|h`. Conversely,
those two conditions make `h+k−R−1=h+4XUλ` a positive multiple of `U`, so
its quotient is a positive natural witness. The `e=1` case makes `U|h`
automatic; for `e=3` or `9`, `mu|h` alone need not do so.

The author's checker and result are pinned. The independent `check.py`
exhausts a separate finite modular core over all `0≤d<mu`, possible
`e∈{1,3,9}`, and positive multiples of `mu`; it also independently recovers
the earlier full-zero negative-control residues by modular Pell powering.
These controls are not a proof for arbitrary `IΣ₁` models. The negative
control has `R=19259`, `n=11720`, `d=4180`, `mu=243`, and carrier residue
292 modulo 729; it fails the compact mask and rank-window hypotheses, so it
does not refute the compact case or an existential witness change.

The first-residue formula is an explicit premise of the standard-integer
criterion. The referenced `solution_residues` theorem introduces an
existential index; transferring its formula to an already selected `n`
requires index uniqueness, or a direct application of the recurrence
residue lemma to that `n`. The packet does not claim this composition in
Lean. It also does not establish `d=0`, `U|h`, the 72-to-76 reverse map,
or an iPRA endpoint. No Lean replay was performed.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-compact-carrier-gap-independent/check.py
```

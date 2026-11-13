# A norm-level obstruction to replacing `f²` by a free input

A possible operation reduction would replace the shared gate `f²=f*f`
with an independently positive variable `h`, retaining `h−1` in the strong
residual. Recovering an old positive witness would require `h` to be a
square. The main and strong norm equations alone do not force that property.

The following ordinary integers satisfy both displayed equations:

```
a = 2                         Delta = a²+4a+3 = 15
c = 3572846569215             g = 13837575261124
i = 1
h = 10863410900978748085986480074788652207849081883376

g² = 1 + Delta*c²
Delta*(h-1) = i²*c⁴.
```

But `h` is not a square: its integer square root is
`3295968886530749410979843`, and `h` lies strictly between its square and the
next square. The
pair `(g,c)` is the 15th positive iterate of the Pell unit
`(a+2)+sqrt(Delta)`, starting from `(1,0)`.

This is a **partial norm counterexample**, not a positive graph zero. In
particular, every actual q-cube graph zero has `beta>0` from transport;
positive `J,w,s` then give `q≥2`, `Y=q³s≥8`, `X=wq≥2`, and
`a=Y*(X+1)≥24`. Thus the example's `a=2` is not an admissible actual-zero
parameter. It does not refute a graph-specific proof that the free input is
a square, nor does it provide a candidate equation or a zero-existence
equivalence.

In fact the transport zero gives the stronger bound `q≥3`: it forces
`C=q−F−alpha>0`, while the witnesses `F` and `alpha` are positive. Therefore
`q≥F+alpha+1≥3`, so `Y≥27`, `X≥3`, and `a≥108`. These sharper inequalities
assume an actual positive tuple satisfying the transport equation, and still
do not make the partial norm example a graph witness.

[`check.py`](check.py) checks both norm identities, the nonsquare interval,
and the recurrence by exact integer arithmetic. It uses explicit failures and
rejects optimized Python. Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-free-square-obstruction/check.py
```

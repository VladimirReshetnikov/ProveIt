# Direct Pell and auxiliary roots: 14 inputs, 79 operations, degree 56

This proposed graph has **14 strictly positive inputs, 79 live operations and
exact degree 56** at the authenticated compact44 ports. It combines the
positive-root substitutions used by the reviewed 79/60 first-root comparison
and the separate 78/60 auxiliary-root proposal, but applies them to the
85/56 graph before its X=q*w substitution. Its positive-zero existence is
therefore equivalent to that of the 85/56 graph for arbitrary integer ports
with `beta>0`, subject to independent review below. It is not a new Lean/iPRA
or PDF/JSON binding theorem, provider replay, or global minimum.

## Both positive root maps

Write

```
b=J*beta, q=b+1, M=q³*b, m=X*Y²,
k=eta+zeta, ell=m*k, D=1+ell*(ell+k).
```

The 85 parent has `Z=M*(ell+k−r_old)` and first residual
`A0_old=M²*((ell+k−r_old)²−D)`. The candidate uses a positive first input
tau with residual `tau²−D`. Other residuals do not use the first-root input.
Since M>0, an old zero gives `tau=|ell+k−r_old|>0`; conversely a new zero
maps back with `r_old=ell+k+tau>0`. This is the reviewed direct-root argument
in `../ordinary14-direct-pell79/` and uses no calibrated witness choice.

For the auxiliary factor put

```
V=f²*(T*c−R)−c, Q=Delta*(f²−1), I=i*c²,
y=V+u,  Fa=y²−Q*(y²−V²).
```

The parent supplies a positive u and computes y; the new graph takes
positive y directly and later reconstructs `u=y−V`. The first and main
norms give `k>2` by the consecutive-square exclusion and then
`k>=8XY²+4` by the reviewed elementary Pell descent. Thus
`c>8XY³`, `Delta<(4XY)²<c³`. The strong residual gives
`Delta*(f²−1)=i²*c⁴>=c⁴`, hence `f²>c+1`. Since `f²|(V+c)`, the values
V=−1,0,1 are impossible; therefore `|V|>1`. The strong norm also gives
`Q=I²>1`. The auxiliary equation `Fa=1` then gives

```
(Q−1)*(y²−V²)=V²−1>0.
```

Hence `|y|>|V|`. In a parent zero, u>0 implies y>V, so y cannot be
nonpositive and is a valid new input. In a candidate zero, y>0 implies
`u=y−V>0`. The algebraic identity
`u*(y+V)=y²−V²` preserves the auxiliary residual, and the other four
residuals are unchanged. These maps combine independently with the first
root maps. Neither assumes the sign of V, an old zero in the reverse
direction, or a machine/decoder premise.

## Count and exact degree

Relative to the 85 parent, the first-root substitution deletes M, the old
shifted root, Z, M² and M²*D: five gates. The auxiliary substitution
deletes `y=V+u`, `y+V` and their product, then adds V² and `y²−V²`: one
net gate. Thus `85−5−1=79`, with all 14 inputs and four fixed leaves live.
The checker reconstructs the exact combined row delta, checks unique
names/topology/liveness and 100 signed substitution controls, and
reauthenticates P72 and P115 port bytes.

With `Y=q³*s`, `deg(Y)<=4`, `deg(X)<=1`, `deg(U)<=6`, `deg(a)<=5`,
`deg(c)<=5`, `deg(H)<=5` and `deg(ell)<=10`. The direct first residual has
degree at most 20. The main cancellation described in the 85 parent gives
A1 degree at most 28. The direct auxiliary residual has degree at most 28,
the strong residual at most 22 and the guard at most 2. Hence the sum of
squares has degree at most 56. A direct all-inputs-equal ray at the
authenticated ports has degree 56 and leader 58796952 modulo 1000000007,
proving exact specialized degree 56.

This improves the named 14-input 85/56 graph by six operations at the same
degree. The separate 14-input 78/60 graph trades one fewer operation for
higher degree. These are comparisons to named records, not global optimality
or a new proof about the displayed 65/150 PDF equation.

```
python3 -I -S -B research/ordinary14-direct-roots79-56/check.py > /tmp/direct-roots79-56.json
cmp /tmp/direct-roots79-56.json research/ordinary14-direct-roots79-56/result.json
```

The finite controls do not replace the unbounded positive-root argument or
the degree upper bound. The inherited compact44 endpoint qualifications
remain unchanged.

Independent mathematical review is recorded in
`../../reviews/ordinary14-direct-roots79-56-math-independent/`.

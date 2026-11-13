# A direct-qF 73-gate probe and proposed actual-port zero

This **proposed probe** has 14 positive inputs, 73 live operations and exact
degree 107 at the authenticated compact44 ports. It deletes the `qF=q−F`
gate of the reviewed [`14/74` positive-guard graph](../ordinary14-positive-guard74/)
and treats qF itself as a positive input. The deletion removes the requirement
that the old `F=q−qF` be positive. The symbolic construction below proposes
a positive zero at the actual ports with old F **strictly negative**. Its
finite scalar checks pass, while the huge binomial/Pell completion is
submitted for independent review. This packet does not establish
unrestricted zero-existence nonequivalence, a parent zero, a Lean/iPRA
theorem, PDF/JSON binding, provider replay or global minimum.

## Literal graph and scalar seed

The exact graph is the 74-parent source with the `qF` row deleted and input
F renamed qF. For any signed assignment, evaluating the old graph at
`F=q−qF` gives exactly the proposed graph's output. Positive qF alone does
not force positive F.

Let the four ports be the P72/P115 authenticated raw integers. Put

```
B=590069, b=beta=2^B−1, q=b+1, J=1,
A=b*q*(q²−1),
G0=3*b*q+1−2*b,
R0=G0*(q²−1)+MC+q*MF,
L=bit_length(R0)+1, S=bit_length(A)+1,
t=2+2^L+2^(L+S),
qF=q+b*t, alpha=1+b*(t−2), C=qF−alpha=3*b,
G=b*qF+alpha, R=G*(q²−1)+MC+q*MF.
```

All these inputs are positive. The old F coordinate would be
`F=q−qF=−b*t<0`. The checker computes the finite integers, authenticates
the port hashes and verifies

```
R=R0+A*2^L+A*2^(L+S),  R=3 (mod 4),
bit_length(R)=7080832,     popcount((R−1)/2)=3540414 >= 3*B+1.
```

The shifted A blocks do not overlap R0 or each other, and `popcount(A)=2B`.
Let `X=2^R`, `w=X/q>0`, and `h=3*(X+K0)+t+1>0`. The last is an
exact finite symbolic expression; X is **not expanded**. Since
`qF=q+b*t` and `q=b+1`, the proposed graph's fifth factor is exactly

```
C*(X+K0)+qF−b*h = 1.
```

Thus the retained transport factor does not exclude this negative old-F
assignment.

## Proposed first, main, strong and auxiliary witnesses

Set `N=(R−1)/2` and

```
Y = (1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),  s=Y/q³,
E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q².
```

The reviewed central-binomial valuation gives
`v2(Y)=popcount(N)−1>=3B`, so s is a positive integer. Using
`(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`, set

```
k=2*psi_(2m+1)(N+1), r=chi_(2m+1)(N+1),
c=psi_(a+2)(R), d=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(d−X−a*c)/H,
gamma=gamma0+(k−R−1)/U.
```

The reviewed binomial/Pell floor argument gives `Y<c/k<Y+1`, so eta and
zeta are positive. The first norm gives `r²=1+m*(m+1)*k²`. Because
`q²|X`, `U|X*Y`; the first Pell congruence gives
`X*Y|(k−R−1)`. The trace identity gives the positive integer
`gamma0>=2^(R−2)`, and `k>=R+1`, so gamma is positive. Substitution in the
modified main carrier yields `Dstar=U*d`, and the main norm vanishes.

For the remaining coordinates use the same aligned-index strong and
auxiliary completion as the independently reviewed
[`compact44 signed-fold witness`](../ordinary13-folded-root86-negated-compact44-seed/):

```
f+L0*sqrt(Delta)=(d+c*sqrt(Delta))^c,
i=Delta*L0/c²,  S0=Delta*L0,
V=chi_S0(R)/S0,  y=psi_S0(R),
T=(V+c+f²*R)/(c*f²).
```

The cited binomial/Pell and same-index Chebyshev arguments give positive
integers f, i, T, y, the strong equality `g72=0` and auxiliary equality
`Fa=1`; the main index is R in both places and `R=3 mod 4`. Together with
the direct first norm and guard factor above, this **purports** to make all
five unit factors +1 at thirteen positive inputs plus qF. Its unbounded
inheritance and every hypothesis remain subject to independent review; the
finite checker does not evaluate these enormous witnesses.

## Same-q, same-rank obstruction only

Any positive 74-parent zero has `C>0` and hence `F+alpha<q`; the reviewed
guard-factor proof derives this from `Fg=1`, positive h, beta and K0. Its
rank scalar obeys

```
G=b*(q−F)+alpha <= b*(q−1)+(q−2)=b*q−1.
```

The seed has `G=b*q*(t+1)+1−2*b > b*q−1`. At the same fixed q and R,
J is fixed by `b=J*beta`, and the rank formula fixes G uniquely. Therefore
no positive 74-parent zero can have this seed's q and R. This does not rule
out a parent zero at other q,R and does not decide unrestricted equivalence.

## Count and degree

The checker pins both graphs and both port bindings, checks that precisely
one source gate was deleted, checks topology/liveness and 160 signed
identities, and verifies the exact finite seed above. All 14 inputs and four
fixed leaves are live. The unchanged degree upper bounds give 107. An
independent-weight ray `input_i=(i+2)*z` at authenticated ports modulo
1,000,000,007 has degree 107 with leader 803341724. The all-inputs-equal
ray has lower degree because direct qF and alpha cancel in C, so it is not a
valid leading-degree certificate here.

```
python3 -I -S -B research/ordinary14-direct-qf73-probe/check.py > /tmp/direct-qf73.json
cmp /tmp/direct-qf73.json research/ordinary14-direct-qf73-probe/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-direct-qf73-probe-independent/`.

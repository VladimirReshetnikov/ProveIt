# Removing the redundant v-square from the signed14 guard

This separate polynomial has fourteen unrestricted integer unknowns,117 live
binary arithmetic operations and exact total degree312. It retains the entire
six-coefficient tuple and the identical degree256 three-root norm of the
frozen119-operation parent. Its new ordinary proof handles v=0 explicitly;
it does not transfer a positive-domain argument to unrestricted integers.
There is no new native calibration, Lean/internal-ZFC proof, consistency
assumption, absence-of-zeros claim or global optimum assertion.

## Complete specification and retained source

Use the complete integer polynomial front in `source/parent-equation.json`,
which is the byte-exact frozen `constructive-integer14-quadratic-shared`
parent, SHA256
`307015e68eb300713d06076b0c3c78f1017fe74dbe79f6b89385292637d1ec41`.
The fourteen coordinates are

```
j,C,z,h,r,v,w,T,c,n,t,p2,p3,p1 in Z.
```

Every fixed coefficient is copied whole under `coefficients/`; MF is the
already shifted port. All base definitions, including the positive beta
and fixed powers cone_A/cone_B, are unchanged. The copied corrected signed
proof is `source/ordinary-proof.md`; the earlier full front, Pair/Pos lemmas
and weak-scale bounds are in `source/ancestor-proof.md`.

For clarity the needed core registers are

```
J=6j+1, q=beta*J+1, W=12w+4, X=qW, Y=qv,
a=(X+1)Y, H=4a+3, Delta=(a+2)^2−1,
k=R+1+hXY, eta=c−Yk, zeta=k−eta,
i=2r+1, I=i*c², Df=1+Delta*I², Q=Delta²*I²,
delta=Q−1, V=Df*(cT−R)−c, Cy=QV²−1,
Dtau=1+XY²(XY²+1)k²,
M=2q², U=MH, K=X(X+2ac)−1,
Z=U(n+V)+MK+H(v−q²).
```

The unchanged three-root norm is the complete integer polynomial

```
N=F8(delta*Z²;delta*U²*Df,delta*U²*Dtau,U²*Cy),
F8(s;u,t,w)=[(s+w−u−t)²−4(sw+ut)]²−64swut.
```

Replace only the old guard by

```
G=(cone_A*F)(cone_B*C)−(q−cone_A*F−cone_B*C)²,
Peta=eta*zeta,
Pair(x,y,t)=xy−(t²−x−y+1)²,
Pos(p1,p2,p3)=1+p1²+p2²+p3(p3+1),
B=Pair(G,Peta,t)−Pos(p1,p2,p3), S=B²,
P=N+S+NS.
```

The new equation is P=0. Unlike its parent, the guard uses G directly,
rather than v²G. No other abbreviation is changed. `equation.json` is a
complete division-free arithmetic DAG with144 live nodes and117 operations.

## 1. What the finalizer and smaller guard actually imply

For integers N,B, the equation N+B²+NB²=0 is equivalent to N=B=0:
`(1+B²)(1+N)=1`, and the first factor is a positive integer divisor of1.
This requires no sign assumption on N.

The elementary Pair lemma says that some integer t makes Pair(x,y,t)>0
exactly when x>0 and y>0. Pos represents exactly the strictly positive
integers; the latter follows from Legendre's three-square theorem, as
proved in the retained ancestor Section3. Consequently B=0 implies

```
G>0, eta*zeta>0.                                           (1)
```

Conversely (1) admits four unrestricted private witnesses t,p1,p2,p3
making B=0. It does not by itself imply v≠0; that missing implication is
proved next from the same norm N.

## 2. Excluding v=0 without the weak-scale estimates

The literal affine restrictions are unconditional: q is even, q=2 modulo3,
q≠0, W≠0, H≠0 and Delta≥3. Suppose a new zero has v=0. Then

```
Y=a=0, H=Delta=3, Dtau=1,
eta=c, zeta=k−c.
```

Thus eta*zeta>0 gives c≠0, and odd i=2r+1 is nonzero. In particular

```
Df=1+3i²c⁴, Q=9i²c⁴≥9, delta=Q−1>0.
```

V=Df*b−c with integer b=cT−R cannot vanish: if b=0, V=−c≠0;
otherwise |V|≥Df−|c|>1. Therefore

```
f=sqrt(Df)>0, y=sqrt((QV²−1)/(Q−1))>0
```

are well-defined. U=6q² is nonzero. The exact three-root product identity
for N gives a signed relation

```
Z/U = epsilon*f + epsilon0*1 + nu*y.
```

Subtract the signed1. The rational number r0 on the left is
`epsilon*f+nu*y`. If r0=0, then f=y. Squaring and substituting gives

```
V²=Df−(Df−1)/Q=Df−1/3,
```

impossible for integer V,Df. Equivalently the equation would give
`3V²−3Df+1=0`, whose left side is1 modulo3. Hence r0≠0, and

```
f=(r0²+Df−y²)/(2*epsilon*r0)
```

is rational, then y is rational. Since Df is an integer, f is integral.
The retained adjacent-coefficient descent applied to
`QV²−(Q−1)y²=1` makes y integral as well. Thus Z/U is an integer and U|Z.

Reduce the literal center modulo M=2q². It gives
`M | H(v−q²)`. Since H=3 and q=2 modulo3, gcd(H,M)=1. With v=0 this
would force `2q² | q²`, impossible for q≠0. This contradiction proves
v≠0 at every new integer zero. No large-|Y| estimate, main-root
classification, gamma or native interpretation was used for this branch.

## 3. Complete integer witness maps

At a new zero we now have v≠0, G>0, eta*zeta>0 and N=0. Therefore
v²G>0. Apply the Pair and Pos lemmas to choose fresh t_old,p1_old,p2_old,
p3_old with `Pair(v²G,eta*zeta,t_old)=Pos(p1_old,p2_old,p3_old)`.
Retain every other coordinate, including unrestricted n. The norm uses
none of these four private guard coordinates, so it is still zero.
This gives an actual zero of the frozen119 parent.

Conversely an old zero has N=0, v≠0,G>0,eta*zeta>0 by its old guard.
Regenerate the four private witnesses for `Pair(G,eta*zeta,t_new)`.
All other coordinates and the identical N remain unchanged, giving a new
zero. Thus integer-zero existence is equivalent in both directions.
The complete old signed proof and its named native/compiler/refutation
calibration apply only after this old zero has been restored. No new
calibration assumption is concealed in the exceptional-branch argument.

These are existential maps, not pointwise equality of the full polynomial,
not a bijection of its zero set and not a claim that the private witnesses
are preserved. The DAG certificate explicitly retires the old Gv register.

## 4. Exact degree and unchanged complete leading component

The norm N is pointwise identical to the parent and has exact degree256.
The old and new guards both have degree28, with leading term
`−LH(eta*zeta)²`; G has degree4, eta*zeta degree14. Pos has degree2.
More strongly, let Bold be the old guard and Bnew the new one. The exact
polynomial identity is

```
Bnew−Bold=(1−v²)*G*[2t²−eta*zeta+2−(1+v²)G].                (2)
```

Its total degree is at most20. Hence

```
Pnew−Pold=(Bnew−Bold)(Bnew+Bold)(N+1)
```

has degree at most20+28+256=304, strictly below312. The entire
highest homogeneous component of degree312 is consequently unchanged.
In particular the parent's actual nonzero selected coefficient remains

```
[j^140 w^48 v^60 h^12 r^16 c^32 z^4] Pnew
    = 2^280 * 3^188 * beta^140 > 0.
```

This proves exact degree312 over the actual integers, rather than merely
transferring the larger syntactic bound344. The complete copied ordinary
norm certificate supplies the degree256 upper bound used here; actual
finite-field line computations are additional exact attainment diagnostics.

## 5. Literal and independent checks

The only removed operations are v*v and its multiplication by G. Every
remaining parent instruction is accounted for by the complete node map;
uses of the old guard argument are explicitly replaced by G. Every node
outside that guard dependency cone, including the entire norm, is identical.
The old named Gv is retired rather than falsely equated as a polynomial.
The result has66 multiplications,26 additions and25 subtractions, all live.

The independent checker imports no new builder. It verifies every row and
operand, the explicit alias and sole-use facts, the entire norm/core
identity, private-variable independence of N, all35 coefficients of its
cleared norm, full old/new guard formulas and difference (2), degree304
of the full difference bound, and the exceptional v=0 algebra/CRT facts.
All six complete fixed payloads are copied byte for byte and checked against
the immutable119 parent. Actual signed assignments include v=0 and c=0;
two actual-tuple line computations attain degrees312 and256. Wrong guard
aliases, finalizer operations and norm operands are rejected. Both checker
and deterministic builder are replayed in normal and optimized Python.

Frozen parents, page files and common documentation remain unchanged.

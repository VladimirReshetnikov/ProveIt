# Free auxiliary-square probe: compact-port partial obstruction

The [85-row eta/zeta-natural probe](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) computes `y2=y*y` once and then uses y only through y2. Deleting that multiplication and using an independent natural input `n_y2` gives the generated **84-row research candidate**. Every parent valuation maps pointwise forward via `n_y2=y²`; the checker verifies that exact graph transformation and 300 modular controls. The reverse zero map is not established.

At the **actual fixed symbolic compact tuple**, the candidate has a standard-natural **partial assignment** with its actual graph rank, strong residual zero, auxiliary factor one and `n_y2` nonsquare. The first and main residuals are not claimed zero. Therefore this demonstrates that strong+auxiliary factors and the rank alone cannot force the auxiliary input to be a square; it does not give a full child zero, refute an existential witness replacement, or prove a consistency equation.

Let `q=2^(67*8807)`, beta=q−1 and use the exact fixed K0, MC and MF. Choose `J=1`, `F=1`, `w=1`, `s=1` and put

```
Y=q³, X=q, a=Y(q+1), A=a+2,
Delta=A²−1, c=Delta+2=A²+1, C=q²−1.
```

Choose natural alpha≥1 so the actual graph rank

```
R=(alpha+beta²)*C+MC+q*MF
```

satisfies `R≡2 (mod c)`. Such alpha exists because `gcd(C,c)=1`: q is even, so q−1 and q+1 are coprime; modulo q−1, c≡17, while modulo q+1, c≡5. The fixed exponent gives q≡15 mod 17 and q≡2 mod 5, so each gcd is one. Take a positive representative of the resulting linear congruence. Then R is positive and `T=(R+Delta)/c` is an integer at least one.

The graph's `k=eta+zeta` and `c=eta+Yk` can represent this c. Since `c=a²+4a+5` and Y>5, set `k=floor(c/Y)`, `eta=5` and `zeta=k−5`; the displayed formula for c makes k>5. All inputs are natural.

The Pell matrix for multiplier A and discriminant Delta has determinant one modulo c², so some positive power h≤c⁸ is the identity. Its pair `(f,v)` satisfies v>0, c²|v and `f²−1=Delta*v²`. Set

```
i=Delta*(v/c²),    I=i*c²=Delta*v,
V=I²−2,            y2=I⁴−3I²+1.
```

Then i>0 and the strong residual is zero because `I²=Delta*(f²−1)`. Also `T*c−R=Delta`, so the actual graph ordinate is `f²*Delta−c=I²−2=V`; direct expansion gives `y2−I²*(y2−V²)=1`, making the auxiliary factor one. Since I≥2,

```
(I²−2)² < y2 < (I²−1)²,
```

so y2 is a positive **nonsquare**. The input for the graph's shifted i is i−1.

For clarity, if the remaining inputs are set to r=gamma=0, the graph still has its exact first and main roots

```
Bt=(beta−alpha)(q+K0)−1,    ell=X*Y²*k,
Z=beta*(ell+k−k*Bt)−Bt,
Dstar=U*(X+a*c)+H*(R+1−k),  U=Yq², H=3+4a.
```

No claim is made that their residuals vanish for the compact assignment. They may impose further constraints, including squarehood, at a full output zero.

The checker pins the parent and compact tuple sources, generates the 84 rows, checks the exact auxiliary polynomial identities, and independently constructs a **finite noncompact toy** at q=2 with a computed Pell period 5151. It evaluates every child row there: strong=0 and auxiliary=1, y2 is nonsquare, and both first/main residuals are nonzero. That toy is a control, not an evaluation of the huge compact witness. The quantified gcd, period and Pell reasoning above supplies the standard-integer partial construction. No huge fixed-compact constant or corresponding Pell iterate is materialized, and no Lean, provider/axiom replay or PDF binding is involved. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-compact-factor-obstruction/check.py | cmp - research/ordinary13-free-aux-square-compact-factor-obstruction/receipt.json
```

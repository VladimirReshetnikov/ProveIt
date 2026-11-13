# Compact-port strong/auxiliary nonsquare partial assignment

For the [84-row free-square candidate](../ordinary13-eta-zeta84-free-square-obstruction/candidate.json), the strong residual and auxiliary factor, even together with the **actual compact graph rank and its natural-coordinate relation** `k=eta+zeta`, do not force `t+1` to be a square. The construction below gives a standard-natural assignment at the fixed symbolic compact ports with strong residual zero, auxiliary factor one, and `t+1≡6 (mod 7)`.

This is a **partial assignment**, not a claimed full graph zero: its actual first and main graph roots are specified below, but their residuals are not asserted to vanish. It therefore does not disprove square forcing from *all four* factors, establish zero-existence inequivalence, or decide the original parent equation. No Lean/iPRA/model theorem or physical-PDF binding is claimed.

Let `q=2^(67*8807)`, beta=q−1, and use the exact fixed natural K0, MC and MF. Choose J=1, F=1, w=1 and s=1. Put

```
Y=q³, X=q, a=Y(q+1), Delta=(a+2)²−1,
c=4*Delta+3 = 4*(a+2)²−1, C=q²−1.
```

The graph rank for natural alpha is `R=(alpha+beta²)*C+MC+q*MF`. We can choose alpha≥1 so that R≡3 mod c. Indeed q is even; modulo q−1 one has a≡2 and c≡63, while modulo q+1 one has a≡0 and c≡15. The source exponent gives `q≡32 (mod 63)` and `q≡2 (mod 15)`. Since q−1 and q+1 are coprime, `gcd(C,c)=3`. Direct modular evaluation of the fixed low/high digit recipes gives `MC+q*MF≡0 (mod 3)`. Therefore `3−(beta²*C+MC+q*MF)` is divisible by gcd(C,c), and the linear congruence for alpha is solvable. Select its positive representative; R is then natural, R≥3 and R≡3 mod c.

Set `k=floor(c/Y)`, `eta=c−Y*k` and `zeta=k−eta`. All are natural: 0≤eta<Y and c≥Y², hence k≥Y>eta. This is exactly the candidate's natural input relation `k=eta+zeta` and actual c=eta+Y*k. Now define

```
v=3*c²,  t=Delta*v²,  L=t+1,
i=3*Delta,  I=i*c²=Delta*v,
T=1+(R−3)/c,  V=4*I²−3,  y=4*I²−1.
```

The graph's `f2` is L. The equation `I²=Delta*t` makes its strong residual zero. Since c=4Delta+3 and `I²=Delta*(L−1)`, one has `V=4Delta*L−c=L*(T*c−R)−c`, exactly the graph's ordinate. The identity `y²−I²(y²−V²)=1` makes its auxiliary factor one. Both shifted inputs `i−1` and `T−1` are natural.

For nonsquarehood, the fixed exponent gives q≡4 mod 7. Hence Y≡1, a≡5, Delta≡6, c≡6, v≡3, and L≡6 mod 7. The only square residues modulo 7 are 0, 1, 2 and 4, so L is not a square.

The other actual graph fields remain as follows: with r=gamma=0, `Bt=(beta−alpha)(q+K0)−1`, `ell=X*Y²*k`, `Z=beta*(ell+k−k*Bt)−Bt`, and `Dstar=U*(X+a*c)+H*(R+1−k)`, with U=Yq² and H=3+4a. No claim that their corresponding residuals vanish is made. The full candidate output remains undecided for this assignment.

The checker pins the child and digit sources, independently obtains the fixed compact modular residues, checks the child row wiring and exact strong/auxiliary polynomial identities, and evaluates every graph row for a finite toy q=32 with the same relevant residue pattern. In that toy the strong residual is zero, the auxiliary factor is one, and both first/main residuals are nonzero; that control is not the fixed compact assignment. The fixed huge constants are never expanded. The modular-inverse and gcd proof above supplies the quantified standard-integer construction, not the finite control. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-square-compact-factor-obstruction/check.py | cmp - research/ordinary13-free-square-compact-factor-obstruction/receipt.json
```

# Independent review: compact free-square partial assignment

The reviewed `research/ordinary13-free-square-compact-factor-obstruction/` gives a standard-natural assignment at the exact symbolic compact ports for which the free-square child's strong residual is zero, auxiliary factor is one, actual rank and eta/zeta coordinate relation hold, and `t+1` is not a square. The first and main residuals are not shown to vanish; this is not a full graph zero or a disproof of square forcing from all factors.

For `q=2^(67*8807)`, J=1, F=1, w=s=1, set `Y=q³`, `a=Y(q+1)`, `Delta=(a+2)²−1`, `c=4Delta+3`, and `C=q²−1`. Modulo q−1, a≡2 and c≡63; modulo q+1, a≡0 and c≡15. The exact exponent gives `q≡32 mod 63` and `q≡2 mod 15`, and the odd factors q−1 and q+1 are coprime. Therefore `gcd(C,c)=1*3=3`. Independent Horner evaluation of the pinned mask digits gives `MC+q*MF≡0 mod 3`, so the linear congruence `R≡3 mod c` is solvable for alpha. Adding the modulus gives a positive representative; the actual graph rank is then natural and at least 3.

With `k,eta=divmod(c,Y)`, `c≥Y²` gives k≥Y>eta, so zeta=k−eta is natural and the exact graph equalities `k=eta+zeta` and `c=eta+Yk` hold. The graph used here has unshifted zeta; this positive zeta would also admit the corresponding shifted coordinate, but no full parent claim follows.

The stated choices `v=3c²`, `t=Delta*v²`, `i=3Delta`, `I=i*c²`, and `T=1+(R−3)/c` are natural with i,T positive. With `L=t+1`, they give `I²=Delta*t`, the strong residual zero, and the actual graph ordinate `L*(T*c−R)−c=4I²−3`. Taking `y=4I²−1` makes the auxiliary factor one by the displayed Pell identity.

For nonsquarehood, the fixed exponent gives `q≡4 mod 7`; direct substitution yields `Y≡1`, `a≡5`, `Delta≡6`, `c≡6`, `v≡3`, and `L≡6 mod 7`. Since 6 is not a square modulo 7, L is not an integer square.

The independent checker pins the relevant graph and digit recipes, reproduces the author's receipt, recomputes the mask residues with a separate Horner evaluation, checks the gcd and nonsquare residues, and evaluates all rows for two finite substitute q values with the required congruences. These finite controls are not the fixed compact assignment or a proof of its first or main factors. No Lean, build, staging, arbitrary-model proof or iPRA conclusion was produced.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-free-square-compact-factor-second-independent/check.py | cmp - reviews/ordinary13-free-square-compact-factor-second-independent/receipt.json
```

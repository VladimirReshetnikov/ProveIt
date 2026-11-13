# Free auxiliary square: nonsquare with a natural main Pell norm

For the [84-row free auxiliary-square candidate](../ordinary13-free-aux-square-compact-factor-obstruction/candidate.json), there is a standard-natural **partial assignment at the actual fixed symbolic compact ports** with all of the following:

* its actual graph rank and `k=eta+zeta` coordinate relation;
* a natural Pell solution of the main norm for its actual a and c;
* strong residual zero and auxiliary factor one;
* the free auxiliary input `n_y2` nonsquare.

The **actual signed main graph root is not shown to equal either signed Pell root**, and the first residual is not shown to vanish. This is not a full child zero, a refutation of square forcing from all four factors, an existential zero-map result, or a Lean/iPRA theorem. It improves on the earlier `c=Delta+2` partial construction, which the [main-norm obstruction](../ordinary13-free-aux-square-partial-main-obstruction/README.md) excludes.

Use the fixed tuple and the independently described [compact rank construction](../ordinary13-free-square-compact-factor-obstruction/README.md): choose `J=1,F=1,w=s=1`, put `q=beta+1`, `Y=q³`, `X=q`, `a=Y(q+1)`, `A=a+2`, `Delta=A²−1`, and choose

```
c = 4*Delta+3 = ycoord(3,a) = 4*A²−1.
```

The fixed source residues give `gcd(q²−1,c)=3` and `MC+q*MF≡0 (mod 3)`. Thus some natural alpha≥1 makes the **actual** graph rank `R=(alpha+beta²)(q²−1)+MC+qMF` satisfy R≡3 mod c; choose a positive representative. Divide c by Y and set k=floor(c/Y), eta=c mod Y and zeta=k−eta. Since c≥Y², these are natural and the graph's `c=eta+Yk`, `k=eta+zeta` hold. The main natural root `g=xcoord(3,a)=4A³−3A` satisfies `g²=1+Delta*c²`.

Choose a positive period of the Pell matrix for A modulo c². It exists because the matrix is invertible in the finite residue ring. Its Pell pair `(f,v)` has v>0, c²|v and `f²−1=Delta*v²`. Set

```
i=Delta*(v/c²),       I=i*c²=Delta*v.
```

Then i>0, I>1, `I²=Delta*(f²−1)`, `I≡0 (mod c)` and `f²≡1 (mod c)`. For a natural u define

```
b = 4+f²*c*u,
V = 1+b*(I²−1),
y2 = 1+2*b*I²+b²*I²*(I²−1).
```

The exact auxiliary identity `(I²−1)*y2=I²*V²−1` holds. Moreover b≡4 modulo both f² and c. Modulo f², `I²≡−Delta` and `c=4Delta+3`, so V≡−c. Modulo c, I≡0, f²≡1 and R≡3, so `V+f²R+c≡0`. The moduli f² and c are coprime, hence

```
T=(V+f²R+c)/(f²*c)
```

is a positive integer. Thus the actual graph ordinate `f²*(T*c−R)−c` is V, the strong residual is zero, and the free-y² auxiliary factor is one. The graph's shifted inputs are i−1 and T−1.

It remains to select u making y2 nonsquare. Choose a prime p≥5 not dividing the nonzero integer `f*c*I*(I²−1)`; such a prime exists. As u ranges modulo p, b ranges over every residue. The displayed y2 is a quadratic in b with nonzero leading coefficient `I²(I²−1)` and nonzero discriminant `4I²`. Its quadratic-character sum over the field is minus the character of its leading coefficient. For completeness, completing the square reduces the sum to `sum_x chi(x²−D)=-1` for nonzero D: the equation `x²−y²=D` has exactly p−1 solutions, one for each nonzero x−y. A nondegenerate quadratic has at most two zeros; if all its values were squares or zero, its character sum would be at least p−2>1, contradiction. Choose the least u in `0..p−1` giving a nonresidue. That y2 cannot be an integer square.

One can set the remaining natural graph inputs r=gamma=0; the actual first and main roots remain

```
Bt=(beta−alpha)(q+K0)−1,  ell=X*Y²*k,
Z=beta*(ell+k−k*Bt)−Bt,
Dstar=U*(X+a*c)+H*(R+1−k),  U=Yq², H=3+4a.
```

The natural main Pell identity concerns g and c; **it does not identify Dstar with ±U*g**. Neither A0 nor A1 is asserted to vanish, and the complete product output remains open.

The checker reproduces the two predecessor receipts, verifies the auxiliary polynomial identity exactly, and tests the character-sum statement over small fields. It also constructs a separate noncompact q=2 toy by explicitly finding an even Pell period (2394), p=29 and u=1, then evaluates every child row; the toy's strong/aux factors hold and both actual first/main residuals are nonzero. The compact constants and compact Pell iterates are not materialized. The quantified finite-field, congruence, Pell-period and integer reasoning above is the proof; the toy controls are not a substitute. No Lean process, build, provider/axiom validation or PDF binding was performed. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-main-norm-nonsquare-partial/check.py | cmp - research/ordinary13-free-aux-square-main-norm-nonsquare-partial/receipt.json
```

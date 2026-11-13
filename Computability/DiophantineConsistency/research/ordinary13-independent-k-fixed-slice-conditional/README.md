# Fixed-port independent-k slice: exact reduction to two remaining conditions

This is a **conditional standard-integer construction**, not a demonstrated graph zero or a proven equation reduction. For the exact fixed symbolic compact ports it constructs a natural child valuation with `eta>k`, the actual graph rank and first residual satisfied, and the strong residual satisfiable. It reduces the remaining positive-main-root and auxiliary requirements to two explicit finite arithmetic conditions. Neither condition is asserted to hold.

Write `rho=2^67`, `beta=rho^8807-1`, `q=beta+1`, and `K0=rho^42*beta+K′`. The separately pinned [kernel bound](../ordinary13-independent-k-actual-rank-boundary-audit/) proves `0<2K′+3<beta`, without expanding the constants. Take the fixed low/high mask ports and choose

```
J=1, F=K′+1, alpha=beta-K′-1, w=1, s=1.
```

All are positive. The actual child graph now has

```
X=q, Y=q³, U=q⁵, C=q-F-alpha=1,
B=beta*h, h=rho^42+1,
G=q*(beta-K′)-1,
R=G*(q²-1)+MC+q*MF.
```

The compact low mask is even and q is even, so R is odd. The compact port bounds and C=1 give `R+q³+q+1≤q⁴`; also R≥27. Put `n=(R+1)/2≥14`, `M=X*Y²=q⁷`, and take first Pell coordinates `(tau,y)` at index n for multiplier `2M+1` and discriminant `4M(M+1)`. Set `k=2y`. The [shared-index growth argument](../ordinary13-independent-k-shared-index-norm-audit/) uses only q≥24 and n≥14 to construct the following actual-rank values:

```
a=Y*(X+1), H=3+4a, Delta=H+a²,
c=ycoord(R,a), g=xcoord(R,a), eta=c-Y*k>k,
k=R+1+4M*sFirst
```

for a natural `sFirst`. Both natural Pell norms and the scalar index/window relations hold. Moreover `tau>M*k`, so the following is a natural first-root input:

```
r=tau-M*k-k+(k*beta+1)*h.
```

The actual first root is then exactly `Z=beta*tau` and `A0=0`.

For the **positive main-root branch**, the exact remaining condition is

```
H | 2^R-q.                                      (main condition)
```

Indeed `xcoord(j,a)-a*ycoord(j,a) ≡ 2^j (mod H)` follows directly from the recurrence and `Delta=a²+H`. Since `U=q⁵` and `k-R-1=U*(4q²*sFirst)`, if the displayed divisibility holds then

```
gamma = 4q²*sFirst + (g-X-a*c)/H
```

is a natural integer and makes the literal `Dstar=U*g`, hence `A1=0`. The quotient is positive: `g-a*c≥c>q=X`. No claim is made about whether the main condition holds for the fixed tuple. Because H is odd and q is a power of two, it can equivalently be written `H | 2^(R-N)-1` once `N=67*8807≤R`; this does not make the condition automatic.

The strong residual can be supplied without an additional numerical condition. The main Pell matrix modulo `c²` has determinant one, so some positive power h returns it to the identity; one may take `h≤c⁸`. If `(f,v)` is its hth Pell pair, then `v>0` and `c² | v`. Set the graph's shifted i-coordinate to `i=Delta*(v/c²)` and its f-coordinate to f. The Pell norm gives `i²*c⁴=Delta*(f²-1)`, so the actual strong residual is zero. This is an ordinary finite-group argument, not a checked internal model construction.

Finally let `I=i*c²`. The remaining auxiliary factor is one if there exist an odd positive index j and sign epsilon in `{−1,1}` such that, for the jth Pell pair `(xj,yj)` with multiplier I and discriminant `I²-1`, the integer `V=epsilon*xj/I` satisfies

```
V+f²*R+c = f²*c*T  for some natural T≥1.        (auxiliary condition)
```

Odd j makes `I | xj`. The displayed condition binds the actual ordinate `V=f²*(T*c-R)-c`; setting the graph's y-coordinate to yj gives its auxiliary factor exactly one. If both conditions hold for these choices, all four factors are +1 and the complete 84-row child has a natural zero with `eta>k`. This is a **sufficient conditional reduction**, not a claim that either condition holds, that the parent has no zero, or that existential zero-equivalence fails.

The checker verifies the exact first-root, rank, main-shift, Pell-congruence-step and auxiliary norm identities as integer polynomials, checks the relevant child rows and runs small recurrence controls. It does not evaluate `2^R`, a huge Pell coordinate, the compact constants, either remaining condition, a Lean proof or a model provider. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-fixed-slice-conditional/check.py | cmp - research/ordinary13-independent-k-fixed-slice-conditional/receipt.json
```

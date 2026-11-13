# Fixed compact independent-k slice: auxiliary condition discharged

For the exact fixed-port construction in the [conditional slice](../ordinary13-independent-k-fixed-slice-conditional/), the strong and auxiliary factors can both be made +1 by explicit ordinary-integer Pell constructions. With those choices and the first factor fixed at +1, a natural gamma completes a **full child zero with `eta>k` if and only if**

```
H | 2^R-q.                                      (★)
```

The divisibility (★) is **not decided** here. This result therefore does not establish a graph zero, failure of existential zero equivalence, a model theorem or an iPRA endpoint. It applies to one explicitly chosen fixed-port slice only.

## Fixed phase and strong witness

Use the preceding slice's exact `J,F,alpha,w,s`, rank R, shared-index first and main Pell coordinates, `eta>k`, and first-root input r. In particular `q=2^(67*8807)`, `a=q³*(q+1)`, `H=3+4a`, `Delta=(a+2)²-1`, and `c=ycoord(R,a)>0`. The exact low-mask digit at index zero is `rho-2≡2 (mod 4)` and all higher digits are multiples of rho, so `MC≡2 (mod 4)`. Since q is divisible by four and the slice has `G=q*(beta-K′)-1`,

```
R=G*(q²-1)+MC+q*MF ≡ 3 (mod 4).
```

Thus `n=(R+1)/2` is even and R is an odd positive index. Let `A=a+2`. The Pell matrix with multiplier A and discriminant Delta has determinant one modulo `c²`, so a positive power `h≤c⁸` is the identity modulo `c²`. Its hth pair `(f,v)` has `v>0`, `f≥1` and `c² | v`. Define

```
i=Delta*(v/c²),  I=i*c²=Delta*v.
```

Then i>0 and I>1. The Pell norm gives `f²-1=Delta*v²`, hence `I²=Delta*(f²-1)` and the graph's strong residual is zero. Moreover `f²≡1 (mod c)` and `I≡0 (mod c)`.

## Auxiliary witness from the same R

Take the Rth Pell pair `(xR,yR)` with multiplier I and discriminant `I²-1`. Since R is odd, `I | xR`; set `V=xR/I>0` and use `y=yR` as the auxiliary coordinate. Define `P_l(t)=T_(2l+1)(sqrt(t))/sqrt(t)` as the integer polynomial determined by

```
P₀=1, P₁=4t-3, P_(l+2)=(4t-2)*P_(l+1)-P_l.
```

The analogous odd-ordinate polynomials `Q_l(A)=ycoord(2l+1,a)` have `Q₀=1`, `Q₁=4A²-1` and recurrence coefficient `4A²-2`. Hence the exact polynomial identity

```
P_l(1-A²)=(-1)^l * Q_l(A)
```

holds by induction. Also `P_l(0)=(-1)^l*(2l+1)`. Here `l=(R-1)/2` is odd. Because `I²=Delta*(f²-1)`, we have `I²≡1-A² (mod f²)`; because `I≡0 (mod c)`, `I²≡0 (mod c)`. Therefore

```
V=P_l(I²) ≡ -c (mod f²),
V=P_l(I²) ≡ -R (mod c).
```

The relation `f²≡1 (mod c)` gives `gcd(f²,c)=1`, so the Chinese remainder theorem yields `f²*c | V+f²*R+c`. Define

```
T=(V+f²*R+c)/(f²*c).
```

The numerator is positive, so T≥1. It satisfies the exact graph ordinate equation `V=f²*(T*c-R)-c`, and the auxiliary Pell norm gives `y²-I²*(y²-V²)=1`. Thus the actual auxiliary factor is +1. The graph input for the shifted T-coordinate is `T-1`.

## Main condition is necessary and sufficient on this slice

The preceding slice establishes `k-R-1=U*(4q²*sFirst)`, so its main root is

```
Dstar=U*(q+a*c+H*(gamma-4q²*sFirst)).
```

The main natural Pell root g satisfies `g²=1+Delta*c²` and `g-a*c≡2^R (mod H)`. If (★) holds, the quotient `(g-q-a*c)/H` is a positive integer: `g-a*c≥c>q`. Choosing `gamma=4q²*sFirst+(g-q-a*c)/H` makes `Dstar=U*g` and the main residual zero.

Conversely, suppose a natural gamma makes that main residual zero. Dividing the displayed root by positive U yields a signed integer d with `d²=g²`, hence `d=±g`. Since N and R are odd, `q≡2 (mod 3)`; therefore `a≡H≡Delta≡0 (mod 3)`, `g≡2^R≡2 (mod 3)` and `d≡q≡2 (mod 3)`. The negative sign would give `d≡1`, so d=g. The root equation and the recurrence congruence then force (★).

All remaining coordinates are fixed independently of gamma, with first and strong residuals zero and auxiliary factor one. The product-output equation is therefore exactly `A1=0` on this constructed slice. Thus (★) is necessary and sufficient for completion by a natural gamma, and if true produces a child zero with `eta>k`. Its truth and the parent graph's zero existence are not determined.

The checker pins the source recipes and both predecessor receipts, certifies the odd-index recurrence induction identities as exact integer polynomials, verifies the fixed R phase from the low digit, and runs small exact Pell/CRT controls including `v>0`, f and I positive and `T≥1`. The uniform proof is the recurrence and CRT argument above, not those finite controls. No giant fixed constants or Pell coordinates, Lean build, model provider or axiom report are produced.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-fixed-slice-auxiliary-discharge/check.py | cmp - research/ordinary13-independent-k-fixed-slice-auxiliary-discharge/receipt.json
```

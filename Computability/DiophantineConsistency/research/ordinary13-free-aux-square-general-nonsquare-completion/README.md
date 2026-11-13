# General nonsquare completion for the free-y² graph

For the [84-row free auxiliary-square candidate](../ordinary13-free-aux-square-compact-factor-obstruction/candidate.json), fix any ordinary nonnegative values of its other inputs and ports for which the actual `a≥0` and `c>0`; let its actual signed rank R be any integer. One can choose **only** the four inputs `f`, shifted i, shifted T, and free y² so that the strong residual is zero, the auxiliary factor is one, and the free y² is nonsquare. The graph's A0 and A1 do not depend on those four inputs and are unchanged. No main Pell norm, choice of main index, or sign/size condition on R is needed for this completion.

Consequently, under the natural port inequalities

```
beta>0, K0>0, MC<beta, MF<2*beta,
```

ordinary-integer existence of a simultaneous `A0=A1=0` valuation is equivalent to existence of a full free-y² graph zero, and also to existence of such a zero with a nonsquare free y². The forward direction uses the [two-norm k-positive transfer](../ordinary13-free-aux-square-two-norm-positive-k-transfer/README.md) to get c>0 and the completion below; the reverse uses the checked first/main modulo-four unit exclusions. This does **not** establish that any of these valuations exists, refute an existential zero-preserving map to the parent, or provide a Lean/iPRA theorem.

## Pell and CRT construction

Put `A=a+2≥2`, `Delta=A²−1`. The Pell matrix is invertible modulo c², so it has a positive identity period; take an **even** positive period h, e.g. twice one. Its pair `(f,v)` satisfies v>0, c²|v and `f²−1=Delta*v²`. Define

```
i=Delta*(v/c²),       I=i*c²=Delta*v > 1.
```

Then `I²=Delta*(f²−1)` gives the strong residual zero, and `f²≡1 mod c`, so gcd(f²,c)=1. Modulo A the Pell pair cycles `(1,0),(0,1),(−1,0),(0,−1)`. Since h is even, `f≡±1 mod A`, so gcd(A²,f²)=1.

Use CRT to choose a natural b0 satisfying

```
b0*A² ≡ 1+c (mod f²),       b0 ≡ R+1 (mod c).
```

For `b=b0+f²*c*u`, u≥0, put

```
V=1+b*(I²−1),
y2=1+2*b*I²+b²*I²*(I²−1).
```

The identity `(I²−1)*y2=I²*V²−1` gives the auxiliary factor one. Modulo f², `I²−1≡−A²`, so V≡−c. Modulo c, I≡0 and f²≡1, so `V+f²R+c≡0`. The moduli f² and c are coprime, hence

```
T=(V+f²R+c)/(f²*c)
```

is an integer and `V=f²*(T*c−R)−c`, exactly the graph ordinate. Increasing u increases T by the positive integer I²−1 each step, so u can be made large enough that T≥1. The shifted graph inputs i−1 and T−1 are natural.

## Ensuring y² is not a square

Choose a prime p≥5 not dividing the nonzero finite integer `f*c*I*(I²−1)`; Euclid supplies one. As u ranges modulo p, b ranges over the field. The displayed y2 is a quadratic in b with nonzero leading coefficient `I²(I²−1)` and nonzero discriminant `4I²`. Its quadratic-character sum is minus the character of its leading coefficient. Indeed, completing the square reduces the count to `sum_x chi(x²−D)=-1` for nonzero D, since `(x−y)(x+y)=D` has p−1 solutions. A nondegenerate quadratic has at most two zeros; if all its values were squares or zero the character sum would be at least p−2>1, a contradiction. Thus some residue u makes y2 a quadratic nonresidue, hence an integer nonsquare. Adding multiples of p preserves that residue and can make T≥1.

The checker follows the exact graph dependencies and verifies neither A0 nor A1 uses any of the four replaced inputs. It reproduces the two predecessor receipts, exhausts small finite-field character controls, and evaluates every graph row in a separate noncompact q=2 toy using a computed even Pell period. In that toy the strong/auxiliary conditions and nonsquare property hold; it is not a claimed compact full zero. The quantified Euclid, period, CRT and character-sum argument above is the proof, not those controls. No fixed-compact giant value, Lean process, provider/axiom replay, parent zero assertion or physical-PDF binding is supplied. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-general-nonsquare-completion/check.py | cmp - research/ordinary13-free-aux-square-general-nonsquare-completion/receipt.json
```

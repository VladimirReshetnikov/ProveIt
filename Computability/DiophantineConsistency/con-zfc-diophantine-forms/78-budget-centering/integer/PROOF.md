# Proof of the integer reductions

## Statement and source

There are three single fixed-coefficient polynomial equations in this package:

- Q26, in 26 unrestricted integer variables, of exact degree 8;
- Q24, in 24 unrestricted integer variables, of exact degree 10;
- Q23,16, in 23 unrestricted integer variables, of exact degree 16.

Each is the sum of squares of its supplied residuals. Composing the reductions proved below with the source71 Q38 correctness theorem gives, by ordinary mathematics formalizable in ZFC, that each equation has an integer solution if and only if ZFC has a finite refutation in the calibrated recursive proof system. Negating gives the requested ZFC-provable equivalence between absence of solutions and Con(ZFC).

The source snapshot is [2605669a532342f153b13eb6b4a0af4b54f5fa37](https://github.com/VladimirReshetnikov/ProveIt/tree/2605669a532342f153b13eb6b4a0af4b54f5fa37). The principal inherited sources, all under `Computability/DiophantineConsistency/con-zfc-diophantine-forms`, are:

- source71 `integer_forms/quartic38.json` and `proofs/DETERMINANT_GUARD.md`;
- source68 `integer_system/PAIR_GUARD_PROOF.md`;
- source64 `integer41/PROOF41.md` and `PROOF44.md`;
- source34 `coefficients/COEFFICIENT_PROOF.md`, builder, exact tile list, and payloads.

The new part is a synthesis followed by two Pell-root translations and the simultaneous elimination of two arithmetic coordinates. It is not a new encoding independent of K215. No global minimum, external priority, end-to-end formal certificate, or consistency proof is claimed.

## 1. Strict positivity and nearest squares

For arbitrary integers p1,p2,p3 put

```
Pos(p1,p2,p3) = 1 + p1^2 + p2^2 + p3(p3+1).
```

This is positive, since an integer product p3(p3+1) is nonnegative. Conversely, every n>=1 has a Pos representation: by the three-square theorem 4n-3 is a sum of three squares. It is congruent to 1 modulo 4, so exactly one coordinate is odd and two are even. Write them as 2p3+1, 2p1, and 2p2, then divide the identity by 4.

For any integers x,y, the source68 lemma says

```
x>0 and y>0
  iff exists t,p1,p2,p3:
       xy - (t^2-x-y+1)^2 = Pos(p1,p2,p3).
```

Soundness is immediate except for the common negative sign. If x=-a and y=-b with a,b>=1, then `(t^2+a+b+1)^2>ab`, contradiction.

For completeness put N=x+y-1 and m=floor(sqrt(N)). Choose t=m if N-m^2<=m and t=m+1 otherwise. For square N the error is zero. For nonsquare N, the integral gap between successive squares gives `|t^2-N|<=m`, and `m^2<N`. In all cases `(t^2-N)^2<N<=xy`, since `xy-N=(x-1)(y-1)>=0`. Represent the remaining positive integer by Pos. The witness-selection square root is not an operation in the polynomial.

## 2. Six fixed integers

The polynomial uses the entire source34 tuple, with no cross-tuple substitutions:

```
beta = 2^1064921-1
K0   = source34 K
MC   = source34 MC
MF   = source34 MF_source   (already shifted by beta)
cone_A = 2^1113
cone_B = 2^666104.
```

Their actual minimal integer bytes, compressed with gzip, are in `coefficients/payloads/`. A byte vector b0,...,b_(n-1) represents sum bi*256^i. `coefficients/NEW_BINDING.json` supplies every raw digest and byte length. `build_and_verify.py` reconstructs all six from the finite source34 recipe, the supplied literal K215 table, and the supplied ordered 943-tile list; it checks equality of complete bytes, not just approximate bounds. Their total minimal raw size is 615883 bytes. None depends on assuming consistency or searching for a refutation.

## 3. Compact definitions and Q26

The 26 independent integer coordinates are

```
J,F,alpha,z,f,h,r,v,w,tau,eta,zeta,y,gamma,o,j,
E,c,a,V,I,u,t,p1,p2,p3.
```

In the JSON, v,w,t are named v_scale,w_scale,pair_root and pi are guardi. Define polynomial abbreviations only:

```
q = beta*J+1
k = eta+zeta
Y = a-E
C = q-F-alpha
X = 2*u^2
H = 4*a+3
delta = a^2+H
T = E*(c-eta)
S = X+gamma*H
R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
G = (cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)^2
Z = eta*zeta
Guard = G*Z-(t^2-G-Z+1)^2-Pos(p1,p2,p3).
```

The fourteen residuals are:

```
A1  = X-4*q*w
A2  = a-E-q^3*(2*v+1)
A3  = E-X*Y
A4  = c-Y*k-eta
A5  = tau^2+(2*tau-k)*T-1
A6  = 2*a*c*S+S^2-H*c^2-1
A7  = k-1-h*E-R
A8  = (K0+4*w)*C-(q-1)*z-F
A9  = V+c-f*o
A10 = V+k-1-c*j-h*E
A11 = I-(2*r+1)*c^2
A12 = I^2-delta*(f^2-1)
A13 = I^2*(V^2-y^2)+y^2-1
A14 = Guard.
```

Q26 is `sum(Ai^2,i=1..14)`. As all residuals are integers, Q26=0 if and only if all fourteen vanish.

To derive it, the source71 Q38 packet has two Pos guard rows for exactly G and eta*zeta. The nearest-square lemma replaces their six private coordinates by four, giving a joint-guard source in 36 variables and 24 rows. Its projection on the other 32 coordinates agrees with Q38's projection. This step is an existential equivalence, not a unique map between guard witnesses.

Translate the old first Pell root and eliminate ten monic definitions:

| Old coordinate | Restoration |
|---|---|
| tau_old | tau+E(c-eta) |
| X | 2u^2 |
| C2 | c^2 |
| F2 | f^2 |
| Baux | I^2 |
| g | y^2-V^2 |
| Delta | a^2+4a+3 |
| D | 2u^2+ac+gamma(4a+3) |
| P | eta+zeta+E(c-eta) |
| L | q^2-1 |
| N | q^3 |

All maps are integer-polynomial maps, with inverse on zero sets obtained by forgetting the defined coordinates and replacing tau_old by tau_old-E(c-eta). The ten monic definition rows vanish identically. Two identities explain the surviving norms:

```
(tau+T)^2-(k+T)^2+(k+T)k-1
 = tau^2+(2tau-k)T-1,

(ac+S)^2-(a^2+H)c^2-1
 = 2acS+S^2-Hc^2-1.
```

The degree of every residual is at most four. Only Guard contains t, and its t^4 coefficient is -1. Consequently `[t^8]Q26=1` on every fixed-coefficient slice. Q26 has exact degree eight.

## 4. Q24 and the two root translations

Now set

```
c = (a-E)*(eta+zeta)+eta
V = f*o-c
y_old = V+nu.
```

Remove c,V from the coordinate list, replace y by nu, delete the now-identical A4,A9, and replace A13 with

```
A13' = (V+nu)^2-I^2*nu*(2V+nu)-1.
```

In all other residuals use the displayed c,V substitutions. Q24 is the sum of the squares of these twelve residuals, with 24 independent coordinates. This is a bijection of the full integer zero sets of Q26 and Q24. Neither positivity nor division is used in its inverse maps.

The auxiliary identity is

```
I^2*(V^2-(V+nu)^2)+(V+nu)^2-1
 = (V+nu)^2-I^2*nu*(2V+nu)-1.
```

Both root translations are essential for the degree count. With c of degree two, T=E(c-eta) has degree three, so an uncentered first Pell root would leave the T^2 term of degree six. Its centered residual is only degree four. With V of degree two, the uncentered auxiliary norm has V^2 of degree four multiplied by I^2; its centered residual is only degree five. The main Pell cancellation already exhibited leaves its substituted residual at degree five. The row `I-(2r+1)c^2` also has degree five.

The twelve residual degrees, in their displayed order, are

```
2,4,3,4,5,4,2,3,5,4,5,4.
```

Only the row A11 contains r. Its square therefore gives the coefficient

```
[r^2*a^4*eta^4] Q24 = 4.
```

No other residual can cancel it. This proves exact degree ten independently of every fixed numeral. The supplied symbolic checker also proves every variable is live.

## 5. Q23,16 by a canonical divisibility restriction

In Q24 simultaneously replace

```
u_old = 2*q*u
w     = 2*q*u^2.
```

Then X=8q^2u^2 and A1 vanishes identically. Delete that residual and the coordinate w. The remaining eleven squares define Q23,16 in 23 unrestricted integers.

Soundness is immediate by integral restoration to Q24. Completeness deliberately uses fresh canonical witnesses. Source64's completeness proof supplies q=2^n, n>=4, an odd R>3q, and u_old=2^((R-1)/2). Since 3*2^n>2n+3, the exponent `(R-1)/2-n-1` is a nonnegative integer. Hence `2q` divides u_old. The relation 2u_old^2=4qw forces w=2qu^2 for u=u_old/(2q). Source71 retains these canonical arithmetic coordinates, and neither the new guard nor the two root translations changes u_old or w.

This is an existence equivalence through canonical witnesses, not a bijection of every old zero. Once X has degree four, the main norm has degree eight through X^2, while the other residuals have degree at most five. The exact leading coefficient

```
[J^8*u^8] Q23,16 = 4096*beta^8 > 0
```

proves degree sixteen on the actual fixed tuple.

## 6. Evidence and limitations

`build_and_verify.py` uses exact sparse polynomial arithmetic. It identifies the literal source guard rows, applies all substitutions, and proves that every nonzero restored joint-source row is exactly one final residual up to sign. Every zero restored row is checked as the zero polynomial. It independently builds the hand-readable formulas above and checks their full equivalence with the transformed rows. It computes the complete sums of squares and checks exact degree coefficients and live variables. It reconstructs all actual coefficients from the literal finite data and compares their complete hashes.

The finite sign and nearest-square sample tests are only diagnostics. The universal positivity proof is Section 1. The native-compiler, Pell-classification and rank, and K215-to-refutation theorems are inherited named unbounded dependencies, not claims established by finite testing. No coefficient is inferred from the absence of a discovered solution. No argument asserts consistency or inconsistency of ZFC.

The source71 theorem and all new transformations are ordinary proofs formalizable in ZFC; a new end-to-end Lean/Rocq theorem or derivation inside the object-language ZFC calculus is not supplied here. The reduction preserves that distinction.

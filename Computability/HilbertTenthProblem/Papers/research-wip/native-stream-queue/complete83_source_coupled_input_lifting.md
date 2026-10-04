# Source-coupled odd-prime lifting in the non-dyadic outer family

This note gives a conditional full completion theorem for the unchanged shared-projection83 source on its actual original five-adic compiler slices. The input representative can realize the relevant odd-prime local roots without freeing X from the source. Exact linear resonance depths can also be arranged while preserving positive outer slack, for every sufficiently large family parameter. Two explicit central-carry conditions remain: a binary population threshold and an odd-prime lower bound. Neither is proved to hold for the constructed z. No full actual-compiler zero or rejected input is asserted.

The new point is quantitative. The Chinese-remainder input representative has modulus at most the odd part of q, rather than its cube, under the stated central-carry hypothesis. Its ordinary input therefore fits the literal slack. This is an existence proof about coordinates of the existing source, not a free POWER, logarithm, factorization, or root-finding operation in a new circuit.

## 1. Exact inherited family and permitted changes

Fix the actual compiler and its constants B=2^d, inner exponent b, K=DC+B*DR, MC, and source MF=MF0+B−1. The original b,d are powers of five. Use the frozen non-dyadic outer-family theorem, with a positive n=1 modulo4, D=dn, Q=B^n, and one of its two shapes:

| Shape | Fixed choice | q | A=odd(q) | t=v2(q) | T | ell=2dT |
|---|---|---|---|---|---|---|
| plus | K!=3 mod5 | Q(Q+1)/2 | Q+1 | D−1 | n(D−1) | 2D(D−1) |
| minus | K=3 mod5 | Q(2Q−1) | 2Q−1 | D | n(D+1) | 2D(D+1) |

J=(q−1)/(B−1) is the same positive integer as in that theorem. In particular A is odd,5 does not divide A, and q is even but not dyadic.

Retain the source-bound forms

```
Z=C=z, F=Kz, W=0,
A0=q^2(q^2−1)+(MC+qMF)J,
G0=(1+qK)(q^2−1),
R(z)=A0−G0*z.
```

The outer-family construction specified a residue class z modulo

```
m0=4d                    (plus),
m0=4d/5                  (minus),
```

which forces z=1 modulo4 and R=b modulo2d. We retain that same class but permit larger positive representatives. No fixed port changes. We subsequently vary the ordinary input while holding q,z,F,R fixed; alpha absorbs that variation exactly as in Section3 below.

For each odd p^a exactly dividing A define

```
tau_p=v_p(D−1)           (plus),
tau_p=v_p(D)             (minus),
b_p=a+tau_p,
g=product_(p|A) p^tau_p.
```

Thus g<=D−1 or g<=D. The elementary lifting identity and the explicit family factorization give

```
v_p(2^ell−1)=b_p.                                 (1)
```

For the plus shape the base exponent is2D, with v_p(2^(2D)−1)=a, and ell/(2D)=D−1. For the minus shape the base exponent is D+1, with v_p(2^(D+1)−1)=a, and ell/(D+1)=2D. These arguments include p=3. No primality assumption on A is used.

## 2. Exact linear resonance depths can be arranged with small z

There exists a positive z in the original m0 residue class such that

```
v_p(r+1)=b_p for every p|A, r=(R(z)−1)/2,          (2)
z <= m0*A*g*(floor(sqrt(3A))+1).                  (3)
```

Positivity of R and all outer coordinates follows under the explicit threshold in Section3; the congruence argument itself can initially use signed integers.

Indeed, at every p|A the factor G0 is−1 modulo p because p divides q. The modulus m0 has only prime factors2 and5, so it is coprime to Ag. Use CRT to choose the least positive z0<=m0*Ag in the original m0 class with

```
R(z0)+1=0 mod(Ag).
```

R is odd throughout this class. Set eta0=(R(z0)+1)/(2Ag), an integer. Along

```
z=z0+m0*Ag*j,
eta=(r+1)/(Ag)=eta0−(G0*m0/2)*j,
```

the coefficient of j is a unit modulo A. Condition(2) is exactly gcd(eta,A)=1.

Here is an explicit elementary bound for finding such a j. Let omega(A) be the number of distinct prime factors. In an interval of L consecutive j, inclusion-exclusion over the primes of A counts the coprime values as

```
L*phi(A)/A + error,     |error|<2^omega(A).
```

Each divisibility condition specifies one residue class because the affine slope is a unit. Furthermore

```
phi(A)/2^omega(A) >= sqrt(A/3).                   (4)
```

To prove(4), divide the Euler product by sqrt(A). For a prime power p^a the resulting factor is p^((a−1)/2)*(p−1)/(2sqrt(p)). Every p>=7 contributes at least1; prime5 is absent; prime3 contributes at least1/sqrt(3). Thus taking L=floor(sqrt(3A))+1 makes the coprime count strictly positive. A j in[0,L−1] gives(2) and(3). This is a finite existence/search argument, not an uncharged circuit producer.

## 3. A fully explicit positivity threshold

Write

```
L_A=floor(sqrt(3A))+1,
Zmax=m0*A*g*L_A.
```

It suffices to choose n in the family such that

```
(K+2)*Zmax + 2d*(5n+T*A) + 1 < q.                (5)
```

All quantities in(5) are fixed finite integers once n and the actual compiler are specified. Such n exist, and all sufficiently large n=1 modulo4 satisfy(5). Explicitly, A<2Q, g<=D+1, m0<=4d, and L_A<=floor(sqrt(6Q))+1, so

```
Zmax <= 8d*(D+1)*Q*(floor(sqrt(6Q))+1).
```

The first term of(5) is therefore O(n*Q^(3/2)) and the second is O(n^2*Q), with constants depending only on the fixed compiler. Meanwhile q>=Q^2/2 and Q=2^(dn). Exponential growth dominates these fixed polynomials. If a wholly elementary search bound is desired, replace Zmax in(5) by the displayed upper bound and test the resulting integer inequality along n=1 modulo4. The all-size dominance proves that search terminates. No arbitrary real-number comparison is required.

Choose a z supplied by Section2. Let x0 be the unique integer in[5n,5n+T−1] with

```
x0=(R−b)/(2d) modT.
```

The source's ordinary input may then be any

```
x=x0+kT, 0<=k<A,
u(k)=2dx+b,
alpha(k)=q−(K+2)z−2dx.
```

By(5), alpha(k)>0 throughout that range. All other outer coordinates remain positive as in the original family, and

```
R=3 mod4, 3q+1<R<q^4−q^3,
0<u(k)<2q<R, u(k)>=10D+b,
R−u(k)=0 mod ell.
```

The index bounds do not reuse the older restriction z<=4d. Directly from the new positive alpha,

```
q^2−Z−qF=q*(2z+alpha+2dx)−z>3q.
```

For the upper bound, F,Z>=1 gives q²−Z−qF<=q²−q−1, while the unchanged actual masks give (MC+qMF)J<(1+2q)(q−1). Substitution into the literal packing gives R<q⁴−q³. Also2dx<q and b<=q give u<2q. These estimates justify the same inherited positive-completion domain for the larger z and input representatives.

In particular X(k)=2^R−2^u(k) is positive and divisible by q(q−1) for every allowed k. With w(k)=X(k)/q, the positive integer transport coordinate is

```
transport(k)=1+z*w(k)/(q−1).
```

It satisfies the literal source transport unit. Varying x here does not secretly vary R: the supplied slack is recomputed, C=Z=z remains fixed, and R's actual producer depends only on q,Z,F and the fixed masks.

## 4. The input map reaches every normalized local residue

Fix an odd p|A, put b0=b_p, and define

```
y_p(k)=X(k)/p^b0.
```

This is integral by(1) and R−u(k)=0 modulo ell. For distinct nonnegative k,k', the exact difference formula and odd-prime lifting identity give

```
v_p(X(k)−X(k'))=b0+v_p(k−k').
```

The powers of2 multiplying the difference are p-units. Consequently, for every h>=1, the map

```
k mod p^h  -> y_p(k) mod p^h
```

is well-defined and injective, hence bijective on the p^h residues. Outside the positive range 0<=k<A, the same integer exponential formula may give negative X; that signed continuation is used only to state this residue lemma. This statement is about the source-coupled exponential map; it is stronger than merely treating X as a free variable. For the roots used below only h<=a is needed, and all representatives k<p^h<=A already lie within the positive range of Section3.

## 5. Conditional simultaneous odd-prime completion

For the fixed r determined by z, let

```
c_p=v_p(binomial(2r,r)).
```

Assume the explicit central-carry condition

```
c_p>=2a for every odd p^a exactly dividing A.       (6)
```

Then one can choose 0<=k<A so that the odd part A^3 divides Y(k)=M_r(X(k))/2.

To prove this, first use(2): v_p(r+1)=b0, whereas every allowed input has v_p(X(k))>=b0. Put eta=(r+1)/p^b0, a p-unit. The linear-resonance numerator from the exact odd-prime theorem is

```
F_p(y)=eta*(r+2)+r*(r+2)*y+r*(r−1)*p^b0*y^2.
```

For these fixed integer coefficients, F_p(y)=eta−y modulo p and its derivative is−1 modulo p. There is a unique unit root modulo every p^h. If c_p>=3a, the source's three-term odd-prime test already passes for every input k: its other two terms have valuation at least c_p because v_p(X(k))>=b0.

Otherwise put h_p=3a−c_p. By(6), 1<=h_p<=a. Require F_p(y_p(k))=0 modulo p^h_p. Section4 converts the unique root residue into exactly one congruence class for k modulo p^h_p. The root is a unit, so it also forces v_p(X(k))=b0 at this prime. The exact normalized valuation is then at least c_p+h_p=3a.

CRT over the deficient primes gives a representative

```
0<=k<Hreq, Hreq=product_(c_p<3a) p^(3a−c_p) <= A.
```

This representative has positive slack by Section3 and passes every odd-prime cube condition. No compatibility with transport is lost, because the entire input progression already satisfies the exact transport period.

Condition(6) is a real remaining hypothesis. The forced b0 low carries do not automatically prove it. For example, the exact identity for r+1=p^b0*h, p not dividing h, is

```
c_p=b0+v_p(binomial(2h,h)).
```

Thus another a−tau_p carries may still be needed when tau_p<a. The method makes no assertion that the z found by the coprime search has those additional carries.

## 6. An input-invariant binary test and conditional full zeros

The large initial representative x0>=5n separates the binary denominator valuations from every possible u(k). Since R+5<q^4<2^(8D+4),

```
v2(r+1)<8D+3, v2(r+3)<8D+3,
u(k)>=10D+b.
```

For odd r, write c2=popcount(r), e2=v2(r−1), j2=v2(r+1), l2=v2(r+3). The valuations of the first four weighted binomial terms are

```
c2,
c2+u−j2,
c2+2u+e2−j2,
c2+3u+e2−j2−l2.
```

All three later values are strictly larger than c2. Terms of degree at least4 disappear modulo2^(3t+1), since X is divisible by the even q. It follows exactly that the binary scale condition holds if and only if

```
popcount(R)>=3t+2.                                (7)
```

R does not depend on k, so this test is invariant under every odd-prime input lift above.

Combining(5), the constructed resonance z, and conditions(6),(7), the selected input representative satisfies q^3|Y. The already accepted outer-family converse then supplies all18 positive witnesses of the unchanged83 source. This is a conditional actual-compiler zero theorem, with noncanonical offset W=0. It is not a proof that conditions(6),(7) occur, not an assertion about a prescribed or rejected input, and not an unconstrained universal83 theorem.

Quadratic local resonances are not needed in this sufficient route. Their deeper r+2 valuation and, especially at p=3, their distinct normalized quadratic congruence cannot be substituted for the linear hypothesis without a separate source-sized construction.

## 7. Scope of fresh corroboration

The helper reads all predecessor sources and receipts only as inert bytes. Its newly written finite checks corroborate the coprime affine-interval bound, the normalized exponential residue bijection, local linear-root composition, and the integer binomial carry identity. The mathematical all-size proof, explicit source bindings, and positive input interval are Sections1–6; finite examples do not replace them. No predecessor helper or full source DAG is executed, and no universal compiler instance or huge Pell tuple is evaluated.

The complete fresh evidence consists of23 literal actual-source row bindings;9,024 affine-interval cases;267 carry-decomposition cases, of which186 additionally compare direct binomial integers;488 binary four-term checks;48 local lifts with1,380 permutation residues and45 direct signed-exponential checks; and eight synthetic fixed-numeral family cases. Three of those synthetic cases meet the sufficient interval threshold. They are not actual compiler instances. One separate local two-prime example exercises a nontrivial shared CRT input: r=251, ell=6, k=12 gives u=77, with deficient primes3 and7 both lifted; its252-term finite sum is checked modulo2*42³. It has no supplied compiler constants and is not presented as a full source zero.

The odd-carry target and input-budget observation were developed in communication with the root agent; Pascal's independent carry identity explains the remaining budget deficit. No quadratic-family obstruction is used as a premise here.

The helper authenticates the following exact accepted inputs, all read inertly:

| File | SHA256 |
|---|---|
| complete83_nondyadic_outer_family.md | 42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23 |
| complete83_nondyadic_outer_family.json | 8041d3661c0cfc9c29ca25c99d08567e45a2ceed3dbca29caf22b792a8c97dd1 |
| complete83_odd_prime_boundary.md | 59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| complete83_shared_projection_math.md | 1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c |
| complete83_even_radix_boundary.md | eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

The first proof supplies the exact fixed-layout bounds and conditional18-witness Pell completion; the odd-prime proof supplies the three-term valuation identity. The actual JSON binds the unchanged source, ordinary input and witnesses. The last three proofs supply the inherited offset, even-radix half-binomial identity and actual compiler recipe. The present proof adds the larger-z construction, its new positivity threshold and the source-coupled input lifts.

# Thirteen integers: trace before radical separation

## Result and comparison

The literal polynomial `trace13_degree1072.json` has **13 unrestricted
integer unknowns**, **190 live binary arithmetic operations**
(118 multiplications, 40 additions, 32 subtractions), and **exact total
degree 1072**. It uses the same six fixed numeral leaves as the incoming
root-fusion package. The comparison point from that package is
`norm13_crt_degree1088.json`, at 13 integers, 195 operations and degree 1088.

The new idea is to extract divisibility from a vanishing radical norm by a
normalized field trace **before** proving that every radical is rational.
This recovers the full scale `Y=(2s+1)q^3` first. Its strong size bound then
removes two devices that the preceding proof needed: the factor `v^2` in
the guard and the factor `Lambda=4H+1` on the main Pell radical. A separate
established first-norm factorization saves one further operation.

The exact conclusion is a two-way integer-solvability equivalence with the
unchanged normalized integer kernel in Section 7 of the root-fusion
report. Composition with that kernel's named ordinary native/compiler and
K215 calibration yields the ordinary theorem, formalizable in ZFC,

`ZFC proves [no integer zero of P_trace] iff Con(ZFC)`.

No proof of consistency, global minimality, or new Lean/object-ZFC proof
artifact is asserted. The new unbounded argument below proves the new
reduction; the full native calibration remains the explicit inherited
mathematical dependency.

## 1. Complete polynomial specification

The unknowns are precisely

`j,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z`.

The six constants are the entire coherent
`mixed-parity-unrounded-1064921` tuple

`beta=2^1064921-1, K0, MC, MF, cone_A=2^1113, cone_B=2^666104`.

The port `MF` is **already** `MF_native+beta`. Its numerical payload is not
shifted a second time. The parent `coefficients/BINDING.json` and payloads
specify all six integers completely; no index is chosen by a halting search.
The new verification independently reconstructs their values from the
943-tile native recipe, as well as checking their byte hashes.

All the following are polynomial abbreviations, not additional unknowns:

```
J=6j+1, q=beta J+1, W=12w+4,
X=qW, Y=qv, E=XY,
a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
F=(K0+W)C-z(q-1), alpha=q-F-C,
R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
k=R+1+hE, eta=c-Yk, zeta=k-eta,
i=2r+1, I=ic^2,
Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
V=Df(cT-R)-c, Cy=Q V^2-1,
L=XY^2 k, Dtau=1+L(L+k),
Dmain=1+Delta c^2, b0=X+ac,
G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
Pair=G eta zeta-(t^2-G-eta zeta+1)^2,
Ag=Pair-1-p2^2-p3(p3+1),
M=2q^2, U=MH,
Z=U(n+V)+M b0+H(v-q^2).
```

For five formal radicands define the ordinary integer polynomial

`F32(x;A0,A1,A2,A3,A4)=product_(epsilon in {+1,-1}^5)
 [x-sum_(i=0)^4 epsilon_i sqrt(Ai)]`.

The displayed product is invariant under every formal radical sign change.
After expansion its coefficients are integral and it contains only even
radical powers, so it is a polynomial in its six displayed arguments.
The square-root notation defines a finite polynomial; it does not add root
operations to the emitted arithmetic circuit.

The new polynomial is

```
P_trace = delta^16 F32(
  Z;
  M^2 Dmain, U^2 Df, U^2 Dtau, U^2 Ag, U^2 Cy/delta
).
```

The denominator is cleared symbolically: the degree of F32 in its last
radicand is at most 16. The supplied 190-operation DAG computes this ordinary
polynomial with only integer leaves, variables, `+`, `-`, and `*`. Its
evaluation is defined even at `delta=0`; the proof below separately shows
that this branch is absent for every assignment to the actual front end.

## 2. Two rational-integrality lemmas

### Lemma 1: adjacent-coefficient descent

If `Q>1` and `V` are integers and `y` is rational, then

`Q V^2-(Q-1)y^2=1` implies `y` is an integer.

**Proof.** Write `y=a/d` in lowest terms, with `d>0`. Multiplying the
equation by `d^2` gives `d^2 | Q-1`. A solution cannot have `V=0`.
If `|V|=1`, then `|y|=1`. Otherwise take positive absolute values of V,y
and use the norm-preserving transformation

```
V'=(2Q-1)V-2(Q-1)y,
y'=(2Q-1)y-2QV.
```

The first coordinate remains integral because `d | Q-1`. The second
coordinate has the same reduced denominator d: its numerator modulo d is
`(2Q-1)a=a (mod d)`. The original equation implies
`y>V` and `(Q-1)y<QV`; hence `-V<V'<V`. The transformed norm excludes
`V'=0`. Repeating with absolute values descends strictly in the positive
integer `|V|` until it reaches 1. The denominator, unchanged throughout,
is then 1. This proves the assertion without any square assumption on Q.

### Lemma 2: a rational-part congruence for radical norms

Let `a1,...,as` be rational numbers, possibly zero or negative, and let
`L1,...,Ls,Z` be integers. Suppose each square root `alpha_i` of `ai`
has the following property: if it is rational, it is an integer. If

`Z = sum_i Li alpha_i`,

then `gcd(L1,...,Ls)` divides Z.

**Proof.** Work in the finite multiquadratic splitting field
`K=Q(alpha_1,...,alpha_s)` and apply the normalized field trace
`pi(x)=Tr_(K/Q)(x)/[K:Q]`. For a rational alpha, `pi(alpha)=alpha`.
For an irrational alpha, its minimal polynomial is `x^2-ai`; its two
roots have zero trace, and transitivity of the trace gives `pi(alpha)=0`.
Thus every `pi(alpha_i)` is an integer, so

`Z=sum_i Li pi(alpha_i)`

is an integer linear combination of the Li. This also covers imaginary
radicals: they are irrational and their rational part is zero. No
independence of square classes or separation of magnitudes is assumed.
Different irrational terms may cancel; that cancellation does not alter
the conclusion.

In our application the first four radicands are integers. The last is
`Dy=Cy/delta`. At `Q=0` it is 1. At `Q>1`, Lemma 1 says that a rational
square root of Dy is integral. Hence all five radicals satisfy Lemma 2.

## 3. Uniform facts before imposing any equation

The specified beta has odd exponent. For every integer j,

`q` is even, `q=2 (mod 3)`, and `|q|>=16`.

Indeed `J=6j+1` is odd and is never zero, while beta is odd and is 1 modulo
3. For `J=1` the value of q is `2^1064921`; for every other allowed J
its absolute value is even larger. Also `|W|>=4`, so `|X|>=64`.

If `v=0`, then `Y=a=0`, `Delta=3` and `H=3`. Otherwise

`|Y|>=16, |a|=|X+1||Y|>=63*16`.

In both cases `Delta>=3` is positive and odd, and H is nonzero and odd.
Therefore `Df,Dmain>=1`. For the integer `u=XY^2`,
`u(u+1)>=0`, so `Dtau=1+u(u+1)k^2>=1` as well.

If `c=0`, then `Q=0,delta=-1,Cy=-1,Dy=1`. If `c!=0`, the odd
integer i is nonzero, so `Q=Delta^2 i^2 c^4>=9`, `delta>0`, and

`Df=1+Delta i^2 c^4>|c|+1`.

Writing `b=cT-R`, either b=0 and `|V|=|c|>=1`, or b is a nonzero
integer and `|V|>=Df-|c|>1`. Consequently

`Dy=V^2+(V^2-1)/(Q-1)>=1`.

We have proved `delta!=0` and positivity of all four non-guard radicands
for every integer tuple, including both c=0 and v=0. Nothing in this step
uses a guard, an accepted history, or a Pell-index theorem.

## 4. The scale is recovered by trace, before squarehood

Suppose `P_trace=0`. Since `delta!=0`, one of the 32 complex linear
factors vanishes. Choose signed roots d,f,tau,g,y so that

`Z=M d+U(f+tau+g+y)`.

Their squares are respectively `Dmain,Df,Dtau,Ag,Dy`. The first four
are roots of integer radicands; the fifth satisfies the hypotheses of
Lemma 1, or Q=0. Lemma 2 now gives

`M | Z`,

because all five coefficients on the right are multiples of M. This
conclusion is obtained without knowing that any individual root is
rational, without assuming `Ag>=0`, and without excluding v=0 in advance.

The exact polynomial identity

`Z=M[H(n+V)+b0]+H(v-q^2)`

therefore yields `M | H(v-q^2)`. Since `Y=qv`,

`H=4(X+1)qv+3=3 (mod q)`.

As q is not divisible by 3 and H is odd,

`gcd(H,M)=gcd(H,2q^2)=1`.

It follows that

```
v=q^2(2s+1),   s=(v-q^2)/(2q^2) in Z,
Y=qv=(2s+1)q^3.
```

In particular v and Y are nonzero, and `|Y|>=|q|^3>=4096`. The proof
has recovered the full original scale, including its odd quotient. This
is the step that allows the two earlier scale-dependent devices to be
removed.

For comparison, a direct check of the exceptional v=0 branch gives
`Z/q^2=6(n+V)+2b0-3`, an odd integer, whereas Lemma 2 makes Z a
multiple of `2q^2`. This is consistent with, but weaker than, the full
scale recovery just proved.

## 5. The unscaled guard and strict radical separation

The four other radicands are positive. If Ag were negative, its radical
would be the only nonzero imaginary term of the vanishing factor. Thus
`Ag>=0`, and hence

`Pair=Ag+1+p2^2+p3(p3+1)>0`.

For integers G,P,t, positivity of
`GP-(t^2-G-P+1)^2` implies G>0 and P>0. It first gives GP>0. If both
were negative, write G=-a,P=-b with a,b>0; the squared quantity would
be `(t^2+a+b+1)^2>ab`, a contradiction. Applying this observation gives
`G>0` and `eta*zeta>0`.

The second conclusion excludes c=0, since at c=0 one has
`eta*zeta=-Y(Y+1)k^2<=0`. We can now use `c!=0,Q>1,delta>0`.

Let

`x=|X|>=64, m=|Y|>=4096, K=|k|, C0=|c|`.

The two nonzero integers eta,zeta have the same sign, so K>=2 and
`theta=eta/k` lies strictly between 0 and 1. Since `c=k(Y+theta)`,

`K(m-1)<C0<K(m+1)`.

Write positive square roots as `d+,f+,tau+,y+` and `g+=sqrt(Ag)>=0`.
Let `a*=|a|`. The estimates `a*>=(x-1)m` and
`sqrt(Delta)>a*-3>xm/2` give

```
f+ > (xm/2) C0^2,      f+ > 3 C0^2,
K(xm^2-1) < tau+ < K(xm^2+1),
tau+ > 2 C0,          f+ > 2 tau+,
Q > Df > Dtau > 1,   Q > C0^2.
```

For example, the second strict ratio follows from
`mK(m-1)^2>4(m^2+1/x)`, which holds at the stated lower bounds and
remains true as m,K,x increase. These bounds precede any Pell-index or
native-decoding argument.

The main root satisfies

`C0/5 < d+/|H| < C0/2`.

Indeed use `sqrt(Delta)>a*-3`, `|H|<=4a*+3` for the lower bound,
and `d+<(a*+3)C0`, `|H|>=4a*-3` for the upper bound.

For the determinant guard, write `Uc=cone_A F`, `Zc=cone_B C`. The
exact identity

`12G=4q^2-[3(Uc+Zc)-4q]^2-3(Uc-Zc)^2`

gives `0<G<=q^2/3<q^2`. Also `eta*zeta<=k^2/4`, so the unscaled
guard satisfies

`g+ < |q|K/2 < C0/10`.

The last inequality follows from `m>=|q|^3` and the strip bound; the
fixed determinant coefficients disappear from this estimate.

Finally set b=cT-R. If b=0, then V=-c and

`C0<y+<C0+1`.

If b!=0, then `|V|>=f+^2-C0>2f+`, and `y+>|V|>2f+`.
After omitting a zero g+, the following orders are strictly
superincreasing (each entry exceeds the sum of all earlier entries):

```
b=0:  g+, d+/|H|, y+, tau+, f+;
b!=0: g+, d+/|H|, tau+, f+, y+.
```

For b=0 the first two sum to less than `0.6C0`, and the first three
sum to less than `1.6C0+1<2C0<tau+`; then use `f+>2tau+`.
For b!=0 use successively `tau+>2C0`, `f+>2tau+`, and `y+>2f+`.

The rational number Z/U is a signed sum of exactly these five
magnitudes, since M/U=1/H. A standard square-class argument now makes
all five roots rational: if one were irrational, some Galois automorphism
would change its sign, and subtracting the conjugate relation would give
a nonempty vanishing signed subsum. Its largest magnitude exceeds the
sum of all smaller magnitudes, which is impossible.

Thus d,f,tau,g are integers, and y is an integer by Lemma 1. This
separation argument is the original large-scale hierarchy; no enlarged
main coefficient Lambda is needed.

## 6. Exact two-way restoration of the unchanged integer kernel

Return to the signed integral relation

`U(n+V)+M b0+H(v-q^2)=M d+U(f+tau+g+y)`.

Modulo H it implies `H | M(d-b0)`. Since gcd(H,M)=1,

`gamma=(d-b0)/H` is an integer.

The recovered coordinates satisfy

```
f^2=Df, tau^2=Dtau,
Q V^2-(Q-1)y^2=1,
(b0+H gamma)^2=Dmain,
Ag=g^2,
Y=(2s+1)q^3.
```

They are precisely the normalized integer kernel from the parent report,
with its old scale coordinate replaced by s and its guard square
coordinate p1 replaced by g. The transport equation already holds
identically. The strong/auxiliary source restoration and the canonical
odd strong normalization are unchanged. In particular the guard now
agrees literally with the parent's unscaled guard; no regeneration of
private guard coordinates is required in this map.

Conversely, take any solution of that normalized kernel. Denote its old
scale coordinate by s and its signed square roots by f,tau,p1,y, with
`d=b0+H gamma`. Set

```
v=q^2(2s+1),
n=gamma+f+tau+p1+y-V-s.
```

Retain every other supplied coordinate. The physical Y, all native
quantities, the whole six-port tuple, and the unscaled guard are unchanged.
Substitution gives

`Z=M d+U(f+tau+p1+y)`.

One of the 32 norm factors therefore vanishes and `P_trace=0`. This
construction is integral, does not search for a refutation, and does not
assume consistency or inconsistency. It proves both existence directions.

Composing with the **same named ordinary calibration** as the parent
kernel gives the requested ordinary ZFC-provable consistency equivalence.
This composition is an inherited proof dependency, distinct from the
finite checks below and from the repository's separate incomplete encoded
object-ZFC derivation.

## 7. Paid arithmetic and exact degree

The preceding CRT evaluator has 195 live binary gates. Removing the
guard multiplier v^2 saves two gates. Replacing `ML=4U+M` by M saves two
more. The exact identity

`XY^2(XY^2+1)k^2 = L(L+k),  L=XY^2 k`

saves one further gate. This factorization is already established in the
Hilbert Tenth research (`complete74_factored_first_norm.md`); its use here
is an implementation reuse, not a novelty claim. The independently counted
complete new DAG has 118M+40A+32S=190 gates. Every gate, all thirteen
unknowns, and all six fixed ports are live. The norms and denominator
clearing are included in this total.

Give each unknown degree one and each fixed numeral degree zero. The
front-end degrees are

```
deg(a)=4, deg(Delta)=8, deg(Df)=14, deg(Q)=22,
deg(R)=5, deg(V)=19, deg(Cy)=60, deg(Ag)=28,
deg(Dtau)=22, deg(U)=6, deg(Z)=25.
```

Set

```
d=M^2 Dmain, e=U^2 Ag,
A=U^2 Df, B=U^2 Dtau, Cn=U^2 Cy,
s0=Un+M b0+H(v-q^2), Z=UV+s0.
```

Their degrees are respectively `14,40,26,34,72`, and `deg(s0)=7`.
Use root weights 7 and 20 for `sqrt(d)` and `sqrt(e)`. In the
biquadratic representation of the cleared three-root norm, the exact
first scalar cut is

`J0=delta(s0^2+2UVs0+d+e-A-B)-U^2(V^2-1)`.

The weighted degrees of the four components in the first register, its
adjusted square, and its adjusted second square are respectively

```
[62,54,67,49],
[134,116,129,121],
[268,250,263,255].
```

These values are checked by exact sparse polynomial expansion over
independent cut variables. The unique top component at the first step is
`2 delta Z sqrt(e)` of weight 67. The final scalar component has unique
highest term `16 delta^4 U^4 V^4 e^2`, of degree 268. The remaining two
quadratic norms square this leading term twice: all competing components
have strictly smaller weighted degree. Thus the full top form is

`2^16 Q0^16 Z0^16 e0^8`.

To prove exact degree after specializing the actual fixed coefficients,
write

```
q0=6 beta j, W0=12w, Y0=q0 v, X0=q0 W0,
a0=X0Y0, i0=2r,
F0=W0 C-q0 z, R0=-q0^3 F0,
k0=R0+h a0, eta0=-q0 v k0,
Q0=a0^4 i0^2 c^4,
V0=-a0^2 i0^2 c^4 R0,
U0=8 q0^2 a0, Z0=U0 V0,
e0=-U0^2 eta0^4.
```

The complete degree-1072 homogeneous part is

`2^112 q0^64 a0^128 i0^64 c^128 R0^16 eta0^32`.

In particular,

`[j^480 w^160 v^192 h^32 r^64 c^128 z^16] P_trace
 = 2^976 3^640 beta^480 > 0`.

The exponents sum to 1072. The h exponent selects the `h a0` term
throughout eta0^32; the z exponent then selects `q0^4 z` throughout
R0^16. All remaining factors are monomials. This proves attainment for
the actual beta, independently of any relation among the other five
constants. It is not a naive syntactic degree estimate.

## 8. Reproduction and evidence

Run from a directory containing the new builder and the unmodified pinned
root-fusion package:

```
python3 build_trace13.py --base inherited/root_fusion --out /tmp/trace13
python3 -O build_trace13.py --base inherited/root_fusion --out /tmp/trace13
```

The standard-library builder authenticates four imported source files,
constructs the literal 190-gate DAG, independently checks topology and
liveness, proves the two carrier identities and first-norm identity in
an exact polynomial ring, and proves the weighted degree and selected
coefficient claims exactly. It also independently reconstructs all six
actual numeral values from their retained tile recipe.

Forty-five full-output modular comparisons use a separately written front
end and a literal formal 32-conjugate product, with 1,755 front-register
comparisons and explicit v=0, c=0 and v=c=0 slices. Those comparisons
are transcription diagnostics. They do not prove the unbounded trace,
separation, or native-calibration statements. The new unbounded reduction
is the mathematical proof in Sections 2--6 above.

The equation SHA-256 is
`962f96211acf9cdcde6366b069b490d6a30246d762ccaf8e3bbfaab8985c9064`.
The emitted JSON's coefficient binding points to the original whole tuple;
an integrating package must preserve or update that relative path without
mixing coefficient families.

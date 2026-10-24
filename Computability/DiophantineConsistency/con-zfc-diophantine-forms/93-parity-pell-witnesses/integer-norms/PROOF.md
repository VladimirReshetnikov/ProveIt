# Odd affine root sums: fifteen and sixteen unrestricted integers

All quantified variables are unrestricted integers. The six coefficient ports
are the complete source34 tuple in `coefficients/BINDING.json`, unchanged from
the authenticated parent `upstream17.json`. The parent's native, Pell and
syntactic-refutation calibration is inherited as ordinary mathematics. The new
conclusions proved here are existence equivalences to that parent. Finite code
checks do not establish consistency or an encoded object-ZFC derivation.

## 1. Parent and common abbreviations

The parent coordinates are

`J,C,z,f,h,r,v,w,tau,nu,gamma,T,c,t,p1,p2,p3`.

Its abbreviations are polynomial expressions:

```
J0=3J+1; q=beta*J0+1; W=4(3w+1); X=qW;
Y=(2v+1)q^3; E=XY; a=(X+1)Y; H=4a+3; Delta=a^2+H;
F=(K0+W)C-(q-1)z; alpha=q-F-C;
R=(q-F)(q^3-q)-C(q^2-1)+(MC+q*MF)J0;
k=R+1+hE; eta=c-Yk; zeta=k-eta;
I=(2r+1)c^2; V=c(Tf-1)-Rf^2; m=XY^2; B0=mk;
s=X+gamma H;
det=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2;
Z=eta*zeta; Pos=1+p1^2+p2^2+p3(p3+1).
```

The parent's five residuals are

```
A1=tau^2+(2tau-k)B0-1;
A2=2ac s+s^2-Hc^2-1;
A3=I^2-Delta(f^2-1);
A4=(V+nu)^2-I^2 nu(2V+nu)-1;
A5=det*Z-(t^2-det-Z+1)^2-Pos.
```

Its polynomial is the sum of their squares. The complete ordinary parent
proof is preserved in `UPSTREAM_PROOF.md`. Write

```
d=c^4; Q=Delta(f^2-1); A=1+m(m+1)k^2; S=k(2m+1).
```

The restored first and auxiliary roots are `tau_old=tau+B0` and
`y=nu+V`. The parent equations say

```
tau_old^2=A; (2r+1)^2*d=Q;
QV^2-(Q-1)y^2=1; A2=A5=0.
```

## 2. Bounds available from the guard alone

For integers x,y, the equation

`xy-(t^2-x-y+1)^2=Pos(p1,p2,p3)`

implies x>0 and y>0. Its right side is positive, so xy>0. If x and y
were both negative, put x=-u,y=-v with u,v>0; the subtracted square is
at least `(u+v+1)^2>uv`, a contradiction. This establishes the direction
needed here without any Pell assumptions.

Consequently `A5=0` gives `det>0` and `eta*zeta>0`. Hence k is nonzero,
`|k|>=2` and `0<|eta|<|k|`. The authentic fixed beta satisfies beta>=17.
Since `3J+1` cannot vanish, `|q|>=beta-1>=16`. Also
`|W|>=4`, `|X|>=64`, and `|Y|>=4096`. Thus

```
|a|=|(X+1)Y| >=63*4096,
Delta=(a+2)^2-1>1,
|c|=|Yk+eta|>|k|(|Y|-1)>1,
|m|=|X|Y^2>1.
```

In particular d>0, A>0 and S!=0. The exact identity

`S^2-4A=k^2-4>=0`

gives `S^2>=4A>A`. All these conclusions precede recovery of any omitted
root. Finally Q=1 is impossible: Q is Delta times the integer f^2-1,
and Delta is an integer greater than one.

## 3. Sixteen integers: two roots and an odd sum

Delete r,tau from the parent and introduce n0. The remaining sixteen
variables, in order, are

`J,C,z,f,h,n0,v,w,nu,gamma,T,c,t,p1,p2,p3`.

Set

```
n=2n0+1; L=n+2B0;
G=n^2+4B0(n-k)-4 = L^2-4A;
U=dG+Q; N2=U^2-4dL^2Q;
B4=(V+nu)^2-Q nu(2V+nu)-1.
```

The equation is

`P16=A2^2+B4^2+A5^2+N2^2=0`.

Every zero has A2=B4=A5=N2=0. Section 2 gives d>0, and L is odd,
hence nonzero. Define rational numbers

`u=U/(2dL), tau_old=(L-u)/2`.

The exact identities

```
U^2-4dL^2Q=N2,
(2dL^2-U)^2-16d^2L^2 A=N2
```

give `d u^2=Q` and `tau_old^2=A`. A rational square root of an integer
is an integer (reduce its numerator and denominator to lowest terms).
Therefore tau_old is integral, and `u=L-2tau_old` is an odd integer.
Set `r=(u-1)/2` and `tau=tau_old-B0`. These are integers, A1=A3=0,
and B4=A4 because the recovered I^2 is Q. This is a parent zero.

Conversely, from a parent zero choose `n0=r+tau`. Then
`L=(2r+1)+2tau_old`, and the universal two-root norm identity gives
N2=0. The other three rows are preserved. Thus P16 and the parent are
existentially equivalent over all integers.

## 4. A three-radical lemma with a parity condition

If three positive rational numbers a,b,c have a nonzero rational signed
root sum, and not all three roots are rational, then one root is rational
and the other two cancel exactly. To prove this, group the three roots by
their classes in Q*/Q*2. Distinct nontrivial square-class radicals, together
with 1, are linearly independent over Q in the corresponding multiquadratic
field. Every nontrivial class must therefore have coefficient sum zero.
With only three roots, either two in one nontrivial class cancel and the
third is rational, or all three nontrivial roots are in the same class and
sum to zero. The latter contradicts a nonzero rational sum.

The eight-factor identity for signed sums of three radicals is

```
Phi(z;a,b,c)=((z^2-a-b-c)^2-4(ab+ac+bc))^2-64abc z^2.
```

It equals the product over all eight sign choices of
`z-e1 sqrt(a)-e2 sqrt(b)-e3 sqrt(c)`. This identity also holds for complex
square roots; it is an integer-polynomial identity.

## 5. Rational Pell integrality

For integer Q>1,V, every rational y satisfying
`QV^2-(Q-1)y^2=1` is integral. This is the source69 adjacent-coefficient
descent, retained with attribution in the parent.

Write y=a/b in lowest terms, b>0. The equation gives `b^2|(Q-1)`.
Change signs to make V,y positive; neither can vanish. If V=1 then y=1.
If V>1, apply

```
V'=(2Q-1)V-2(Q-1)y;
y'=(2Q-1)y-2QV.
```

The first coordinate is integral because b divides Q-1. The norm is
preserved, and the reduced denominator of y' is still b, because
`2Q-1=1 (mod b)`. The inequalities y>V and QV>(Q-1)y imply
`-V<V'<V`. The preserved norm excludes V'=0. Absolute values therefore
give a smaller positive integer first coordinate with the same denominator.
Induction reaches V=1, proving b=1. This is an unbounded descent, not a
finite numerical assertion.

## 6. Fifteen integers: three roots and one parity condition

Delete r,tau,nu from the parent and introduce n0. The fifteen variables are

`J,C,z,f,h,n0,v,w,gamma,T,c,t,p1,p2,p3`.

Set

```
n=2n0+1; L=n+2B0+2SV; delta=Q-1; D=d delta;
Aa=4A D; Bb=Q delta; Cc=4S^2 d(QV^2-1);
R3=D L^2-Aa-Bb-Cc;
T3=R3^2-4(Aa Bb+Aa Cc+Bb Cc);
N3=T3^2-64Aa Bb Cc D L^2;
Gsum=A2^2+A5^2.
```

The final single polynomial is

`P15=Gsum+N3+Gsum*N3=(1+Gsum)(1+N3)-1`.

Since Gsum>=0 on every integer tuple, P15=0 forces Gsum=N3=0 by the
integer-unit argument. Conversely those equations imply P15=0.

The guard bounds give D!=0. Dividing N3 by D^4 identifies it with
`Phi(L;4A,Q/d,4S^2(QV^2-1)/(Q-1))`. L is always an odd integer.

* If Q<0, the middle radicand is negative and the others positive. Every
  signed root sum has a nonzero imaginary part, so the norm cannot vanish.
* If Q=0, the middle root is zero and the last roots are +/-2S. A vanishing
  factor makes L=+/-2sqrt(A)+/-2S. Rational-square integrality makes sqrt(A)
  an integer, contradicting odd L.
* Q=1 has already been excluded.
* If Q>1 and V=0, exactly the last radicand is negative; again no factor
  can vanish at a real L.
* If Q>1 and |V|>=1, all radicands are positive. The last is at least
  4S^2>=16A>4A, so the first and last radicals cannot cancel.

In the last case, apply Section 4. If two nonrational roots cancel, the
remaining root is either a rational value +/-2sqrt(A), hence an even integer,
or a rational value +/-2S*y, where y satisfies the norm of Section 5 and
is therefore an integer. This again gives an even L. Cancellation of the
first and last roots is ruled out by their strict size inequality. Hence
all three signed roots are rational.

Write their sum as `L=2tau_old+u+2S*y`, allowing signed roots and allowing
S itself to be negative. Square integrality gives integer tau_old with
tau_old^2=A, and Section 5 gives integer y. Thus
`u=L-2tau_old-2S*y` is an odd integer, with d u^2=Q. Reconstruct

```
r=(u-1)/2; tau=tau_old-B0; nu=y-V.
```

These are integers and satisfy every parent residual. Conversely a parent
zero gives `n0=r+tau+S*nu`, hence
`L=(2r+1)+2tau_old+2S*y`; one norm factor vanishes and P15=0. No
coordinatewise bijection is claimed for this root-merging projection.

## 7. Exact dimensions, degree and arithmetic count

The complete JSON packets list all coordinates, aliases, residuals, and the
single final polynomial. The division-free circuits count each binary
addition, subtraction, multiplication, scalar multiplication and square.
Reuse and fixed integer leaves are free. Neither degree nor gate count is
asserted minimal.

* P16 has sixteen variables, degree 112, and 120 live operations.
* P15 has fifteen variables, degree 310, and 137 live operations.
* Its further centered version has fifteen variables, degree 306, and 140
  live operations; it is a separate degree/cost tradeoff.

The homogeneous source leaders are, writing only top total-degree parts,

```
m0=2^4*3^8*beta^7*J^7*w*v^2;
k0=2^3*3^5*beta^4*J^4*h*w*v;
Q0=2^6*3^10*beta^8*J^8*w^2*v^2*f^2;
V0=f^2(324 beta^3 J^3 w C-81 beta^4 J^4 z).
```

Their degrees are 10,7,14,7. The first norm N2 has degree 56 and leader
`16c^8 m0^2 k0^4`; all other P16 rows have degree at most 44. Therefore
the coefficient of `c^16 J^60 w^12 v^16 h^8` in P16 is exactly
`2^48*3^72*beta^60>0`.

For N3, full exact expansion over the six generic symbols m,k,V,Q,d,n,
with weights 10,7,7,14,4,1, gives 3,120 terms and weighted degree 222.
Its unique weighted-leading monomial is
`2^18*m^8*k^8*V^6*Q^2*d^4`. This calculation includes the leading
cancellations that naive gate-degree propagation misses. Thus the actual
N3 leader is `2^18*m0^8*k0^8*V0^6*Q0^2*c^16`. Gsum has degree 88,
with the guard-square leader inherited unchanged. Their product has degree
310 and coefficient `2^118*3^212*beta^184>0` on
`c^16 J^184 w^28 v^44 h^16 z^6 f^16`. This coefficient is independent
of the other five ports and stays nonzero for the authentic beta.

### A further integral center

Replace `n=2n0+1` by `n=2(n0-hYR)+1` in P15. This preserves oddness
identically and is an invertible integral coordinate shear. Its completeness
map is `n0=r+tau+S*nu+hYR`. All soundness cases above are unchanged.

The independent exact expansion in `independent_degree/audit.py` uses
the genuine formulas on eight independent atoms X,Y,R,h,f,c,T,n0, with
weights 2,4,5,1,1,1,1,1. The entire inner polynomial T3 has 61,891 terms,
weighted degree 109, and complete leading form

```
512 X^9 Y^13 R^3 h^3 f^6 c^8 [R f^2+hY(X-2f^2)].
```

The triple tail of N3 has degree at most 212. Hence N3 has degree 218
and the unit-product polynomial has degree 306. After authentic source
substitution its nonzero coefficient on
`J^184 w^26 v^42 z^8 h^14 f^16 c^16` is
`2^112*3^210*beta^184`. The full argument is in
`independent_degree/NOTE.md`; its coordinate labels J3,w3,v_scale denote
this component's J,w,v respectively. The centered literal costs three
additional gates, because n can be evaluated as `2*(n0-h*Y*R)+1`.

## 8. Modulus-four refinement

`MOD4_PROOF.md` gives three additional complete equations, retaining all
the odd-sum equations above. They have respective metrics 16 variables /
degree 112 / 119 operations, 15 / 310 / 136, and 15 / 306 / 139.
The additional source facts are B0=0 modulo four and A=1 modulo four,
because m=XY^2 and X is divisible by four. Choosing a sum congruent to
two modulo four saves one multiplication. Completeness may change the sign
of the private first Pell root; every other parent coordinate is preserved.
The exact new formulas, all soundness cases, sign choice, witness maps and
degree certificates are in the linked proof. The main checker verifies all
six literal packets and invokes the independent degree audit for both
centered variants.

## 9. Scope and attribution

The two-root and three-root norm identities are elementary classical
algebra. The new construction uses an odd affine sum to recover an odd
integer multiplier after eliminating its witness, and uses parity to rule
out partial cancellation among the three radicals. The rational Pell
integrality theorem is inherited and explicitly attributed above.

The new existence equivalences compose with the parent's unbounded
native/compiler/Pell and finite-refutation calibration to give the requested
ordinary theorem formalizable in ZFC. This package does not prove Con(ZFC),
claim a global optimum, supply a newly kernel-checked endpoint, or supply an
encoded object-language ZFC proof. Independent AI review is not external
human peer review.

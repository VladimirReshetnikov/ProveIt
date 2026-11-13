# Free J: automatic elimination of the exceptional factor three

## Result

Replace `J=6j+1` in the current twelve-positive ordinary polynomial, or
`J=3j+1` in the thirteen-positive ordinary polynomial, by a positive input
J. Keep every other definition and the whole compact44 tuple unchanged.
The resulting circuits have **12 positive inputs, 98 operations, degree70**
and **13 positive inputs, 88 operations, degree51**.

Parents at a88aefd7ddab4771534bb049c67350e397c91b9a, under
`Computability/DiophantineConsistency/research/ordinary-unit-products`:

* p12_ordinary_degree70.json, SHA256
  444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010;
* p13_ordinary_degree51.json, SHA256
  c9f5f495249ed13d30393fec5838a85408889d214d2253615f4ba6f60414cf71.

The new source files delete the first multiplication and addition, promote
their former output J to an input, and rename the input list accordingly.
The coefficient tuple is the authentic compact44 beta=2^590069-1, K0, MC,
already-shifted MF. This is an ordinary proof for a larger positive domain,
not a polynomial identity with the old restricted-domain construction.
It inherits exactly the same native/compiler/refutation calibration.
No new Lean or encoded internal-ZFC proof is claimed.

## 1. Shared equations and unrestricted unit recovery

Use the complete parent definitions with J positive directly:

```
q=beta J+1, C=q-F-alpha, E=XY, k=eta+zeta, c=kY+eta,
a=(X+1)Y, A=a+2, H=4a+3, Delta=A²-1,
ell=EkY, M=q³(q-1), W=(q-1)k+1,
Bt=(qK0+X)C-qF,
Z=M(ell+k+r)+(q-1)Y-q³W Bt,
A0=Z²-M²[ell(ell+k)+1],
R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
v=k-R-1, U=q²Y,
Dstar=U(X+ac)+H(U gamma+qE-v),
A1=Dstar²-U²(1+Delta c²).
```

The twelve-variable tail has `f=t+1`, `Q=Delta(f²-1)`, `d=c⁴`,
`V=f²(cT-R)-c`, `h(z)=(1-Q)z²+2(1-Q)Vz+V²-1`,
`bn=2(1-Q)(n+V)`, `AN=d h(n)+(1-Q)Q`, `N=AN²-d bn²Q`, and
`P12=(1+A0)(1+A1)(1+N)-1`.
The thirteen-variable tail has `I=ic²`, `Q=Delta(f²-1)`, the same V,
`y=V+u`, and `P13=(1+A0)(1+A1)[QV²+(1-Q)y²][1+I²-Q]-1`.
All names other than the listed inputs are polynomial abbreviations.

No parity hypothesis on q is needed. M is always even. Delta is 0 or3
modulo4, hence `1+Delta c²` is 0 or1 modulo4. Thus A1 is never2 modulo4.
Also bn is even, so N is a square modulo4. Consequently none of
`1+A0,1+A1,1+N` can be -1. For P13, Q is 0 or1 modulo4, its auxiliary
factor is a square modulo4, and `1+I²-Q` is 0,1 or2 modulo4. The original
unit-product proof therefore gives A0=A1=0 for arbitrary positive J.

## 2. Recover q^4 divisibility without coprimality

The unchanged first-carrier proof, using positivity and authentic masks,
gives `C>0`, `q³|Y`, `q-1|Bt`, `q>=16`, and `3q<R<q⁴-2`.
The unchanged positivity estimate gives Dstar>0. Rational-square-root
integrality gives positive integral D=Dstar/U, with
`D²-Delta c²=1` and `U|H(qE-v)`.

**Lemma.** If q³|Y and H=4Y(X+1)+3, then
`gcd(q,H)=gcd(q^5,H)=gcd(q,3)`, which is either1 or3.

**Proof.** H is3 modulo q³, so all primes dividing q other than3 are
prime to H. If3 divides q then27 divides Y, hence H is3 modulo27 and
v_3(H)=1. This proves both gcd identities. ∎

Since q^5|U, it follows that `q^5/gcd(q,3)` divides qE-v. This quotient
is divisible by q^4, because gcd(q,3)|q. Also q^4|qE=qXY. Therefore
**q^4|v**, with no condition on J modulo3.

## 3. Early rank and ordinary integrality

Put P0=2XY²+1. First/main Pell classification gives positive n0,p with
`k=2 psi_P0(n0)`, `D=chi_A(p)`, `c=psi_A(p)`.
Since P0>A and c>k, we have p>n0. The recurrence gives
`k=2n0 (mod4XY²)`, so `2n0=R+1 (modq^4)`. As `0<R+1<q^4`, the
quotient is nonnegative and `n0>=(R+1)/2>=25`, since R>3q>=48.
Thus p>=6 and

```
psi_A(6)-A(A²-1)²=A(31A⁴-30A²+5)>0
```

gives c>A Delta². The remaining early bounds c>2p and c>2R are unchanged.
All these steps precede the strong and auxiliary equations.

The ordinary strong-rank theorem and auxiliary-index proof now apply
literally as in the parent, including the rational descent reconstructing
i and y from N in the twelve-variable version. They give p=R; these
arguments do not use coprimality of q with3. Because n0<R and
`2n0=R+1 (modq^4)` with `0<R<q^4-2`, it follows that R=2n0-1 exactly.
Then v=k-2n0 is a positive multiple of4XY²; in particular U|v.

From U|H(qE-v), obtain q|HX, hence q|3X, and

```
q(D-ac-X)=H[q(gamma-v/U)+X].
```

Set g=gcd(q,H) in {1,3}. Thus H/g divides D-ac-X. The standard main Pell
projection, with H odd, is `chi_A(R)-a psi_A(R)=2^R (modH)`. Therefore
**X=2^R (mod H/g)**. We must prove equality before recovering q|X.

## 4. Sharpened Pell growth excludes a false projection

Write R=2r0+1. Here r0=n0-1>=24. Pell growth gives

```
c/k >= ((2A-1)²/(2P0))^r0 /2,     c/k<Y+1.
```

The exact identity

```
X(2A-1)²-2P0(X+1)²
  =12XY(X+1)+9X-2(X+1)²
```

is positive for X,Y>=1: its right side is at least10X²+17X-2>0.
Consequently `Y+1 > [(X+1)²/X]^r0/2`.

If X>=2, then `(X+1)²/X>=9/2`. The explicit inequality
`9^16>6*8^16`, together with r0>=24, gives Y>2^(2r0+1)=2^R.
Both X and2^R are then in(0,a), whereas H/g>=H/3>a. Their congruence
therefore gives **X=2^R**.

If X=1, the same ratio gives `Y+1>2^(R-2)`, hence integer
`Y>=2^(R-2)`. Now H=8Y+3 and `0<2^R-1<H/2`.
The congruence modulo H/g is impossible if g=1. If g=3, the only possible
positive multiple below H/2 is H/3. This would force
`8Y=3*2^R-6`, impossible modulo8 since R>=3. Thus X=1 is excluded.
Every positive solution satisfies X=2^R.

## 5. Mersenne coefficients eliminate the exceptional factor3

Since q|3X=3*2^R, q equals2^u or3*2^u. Write beta=2^d-1 with d>=4,
as in compact44. Because beta|q-1, the second option implies
`3*2^u=1 (mod 2^d-1)`. Reduce u modulo d to r in{0,...,d-1}.
For r<=d-2, `3<=3*2^r<=3*2^(d-2)<2^d-1`, so its residue is not1.
For r=d-1 the residue is2^(d-1)+1, also not1. Hence q=2^u and **q|X**.

Restore w=X/q and `gamma_old=gamma+w-v/U`. The latter is integral and
positive: `D-ac=2c-psi_A(R-1)>c>X`. Every other deleted source coordinate
is restored by the unchanged ordinary parent proof. Its whole-tuple
native/compiler/K215 calibration yields a finite ZFC refutation.

Conversely, canonical refutation witnesses already have positive J.
Keep it directly instead of writing it3j+1 or6j+1; all other completeness
constructions are unchanged. Both existence directions therefore hold.
Negating gives the same ordinary Con(ZFC) equivalence, with the same
formalization boundary as the parents.

## 6. Exact counts and degree

The two deleted rows are one scalar multiplication and one addition.
Every retained gate, input, and fixed port stays live. Degrees70 and51
remain exact: in the parents' leading homogeneous coefficients replace
6 beta or3 beta by beta. Those nonzero coefficient arguments are unchanged.

The numerical gain is modest. The new mathematical point is that Pell
growth and the authentic Mersenne coefficient exclude the factor3
automatically; the former congruence restriction on J was unnecessary.

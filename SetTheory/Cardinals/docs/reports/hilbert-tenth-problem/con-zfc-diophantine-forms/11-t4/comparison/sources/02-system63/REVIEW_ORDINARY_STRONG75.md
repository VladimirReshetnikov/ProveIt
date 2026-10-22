# Independent mathematical challenge of the ordinary-strong variant

This review concerns the proposed 75-gate polynomial obtained from the
fixed-input73 definitions by replacing only the auxiliary coefficient,
strong factor, and final constant. All sixteen unknowns and the five
fixed coefficient ports are retained. This is a mathematical and literal-source
review. Independent checks are in `ordinary_strong_review_checks.json`.

Write I=i*c^2 and A0=Delta*(f^2-1). The revised factors are

```
Ns = 1 + I^2 - A0,
Na = A0*(V^2-y^2)+y^2,
P75 = N0*N1*Na*Nk*Nt*Ns*M-1.
```

## Verdict

The variant is sound provided the same pinned generic strong-rank and
signed step-down lemmas are retained, with the proof order below. It
reduces the exact polynomial degree to101. Its seven-equation version
can compare I^2=A0 directly and should retain63 arithmetic gates with
largest equation degree28; the sum-of-squares degree is56. No claim of
a positive-zero-set bijection with the normalized73 variant is needed.

## 1. Recover signs in a noncircular order

A positive zero makes every integer factor a unit. M is positive, so
M=1 and the budget remains q=F+2Z+alpha+W0. The first norm sign and main
norm sign are recovered exactly as in the73 construction.

For the new strong factor, Delta is0 or3 modulo4. If Delta=0 modulo4,
then Ns=1+I^2 modulo4, which is1 or2. If Delta=3 modulo4, then
Ns=I^2+f^2 modulo4, which is0,1,or2. Thus Ns cannot be-1, and Ns=1.
Only now conclude

```
I^2=Delta*(f^2-1)=A0.
```

The auxiliary coefficient is consequently a square. Therefore Na is
y^2 or V^2 modulo4 and cannot be-1; hence Na=1. The index and transport
factors are the only remaining potentially negative units.

## 2. Bootstrap before using auxiliary positivity or rank

The budget and genuine mask bounds give
`(2q-1)(q^2-1)<R<q^4-q^3`, q>=16, E>=q^4>R+2, a>R+2.
The first Pell equation and signed index factor give
`k=2*psi_(2XY^2+1)(n)` and `n>=(R-1)/2>=24`.
The positive main Pell equation gives `c=psi_A(p)`, where A=a+2.
Since 2XY^2+1>A and c>k, one obtains p>n, hence

```
c>A*Delta^2, c>2p, c>2R.
```

None of these inequalities uses auxiliary positivity, an input norm,
the strong-rank conclusion, or the exact index p=R.

Now the ordinary strong equation implies

```
f^2=1+i^2*c^4/Delta > c^4/Delta.
```

The already proved c>A*Delta^2 implies f>2c, c>Delta, and f^2>Delta+c.
Also R<a<Delta. Thus

```
A0-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.
```

Using Na=1, the identical auxiliary gap argument from the73 proof
excludes negative V with |V|>1. The congruence V=-c modulo f and
2<c<f/2 excludes V=0,+1,-1. Consequently V>0.

## 3. The rank lemma gives the exact needed integrality

The pinned generic strong-rank lemma applies to

```
c=psi_A(p), c>A*Delta^2, (i*c^2)^2=Delta*(f^2-1).
```

Its conclusion is stronger than merely c|m:

```
f=chi_A(m), p|m, c|m, i*c^2=Delta*psi_A(m).
```

Most directly, `f^2-1=Delta*psi_A(m)^2=i*c^2*psi_A(m)`, so c^2 divides
f^2-1. Alternatively p|m and Pell divisibility give the same conclusion.
This is the specific fact needed for the following restored integer:

```
o=cT-Rf,
j=Tf-1-R*(f^2-1)/c.
```

One must not infer this simply from c|m. Nor should one assume Delta|i,
which is not guaranteed for arbitrary ordinary-strong solutions.

The identities of-c=V and jc=V+R show o,j>0. The signed step-down
lemma now has its full premises: m>=c>2p, 0<R<c/2, and
V=of-c=jc-R>0. Hence p=R. The same no-wrap and ratio contradiction
as in73 makes the index factor positive; the transport factor is then
positive by the total product sign.

## 4. Restore raw75 directly

All power recovery, fixed-marker and raw-slack arguments are unchanged.
The restored ordinary strong coefficient is simply i_raw=i, because
the raw75 source uses the ordinary strong equation. The auxiliary
coefficient is A0=(i*c^2)^2. The restored o,j just proved positive give
its two auxiliary equations. Every other restored raw75 coordinate is
exactly as in the73 proof. This establishes soundness without a
possibly nonintegral attempted conversion i_normalized=i/Delta.

For completeness, an accepted instance has a normalized73 tuple. Map
its normalized strong coordinate i_n to the ordinary coordinate
`i_o=Delta*i_n`. All other supplied coordinates stay fixed. At that
tuple, A0 equals the old normalized auxiliary square, Ns=1, and all
other unscaled factors equal1. This constructs a positive P75 zero.
No inverse tuple map is asserted.

## 5. Independent degree calculation

Let Q=(B-1)J and k0=eta+zeta. The degrees in factor order
N0,N1,Na,Nk,Nt,Ns,M are

```
22,18,28,7,2,22,2.
```

Their top homogeneous product is

```
8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4
  *(wZ-tQ)*(Q-F-2Z-alpha)^2.
```

The monomial `J^58 h gamma i^2 eta^9 w^7 s^16 t T^2 f^4`
has coefficient `-8(B-1)^58`. Thus degree101 is exact uniformly for
every admissible B>1. The seven-equation version has the unique largest
residual Na-1 of degree28, so its sum of squared residuals has exact
degree56.

For its computation cost, the ordinary system uses four gates for
I=i*c^2, I^2, f^2-1, and A0=Delta*(f^2-1), and directly compares I^2
with A0. The normalized system also used four gates for its strong
comparison. Thus the ordinary seven-equation system can keep the
same63-gate,16-variable interface, while the polynomial pays two
additional additions to form the unit factor and reaches75 gates.

## 6. Literal-source checks

The frozen ordinary source replaces the normalized strong block by the
six paid rows for f^2-1, A0, I, I^2, I^2+1, and Ns, and changes the
final subtraction from Delta to1. All other formulas are retained. The
polynomial ledger is41 multiplications and34 additions/subtractions;
the seven-equation ledger is34 and29. Every gate, witness and fixed
port is live.

An independent exact univariate expansion attains degree101 with the
predicted leader. Ninety-six signed assignments check the two local
off-zero identities under i_o=Delta*i_n:

```
Ns_ordinary = 1+Delta-Ns_normalized,
Na_ordinary-Na_normalized = (Ns_normalized-Delta)*(V^2-y^2).
```

All shared factors and the ordinary system's comparison operands
coincide under the specified source maps. Exhaustive modulo-four
checks cover32 strong-sign cases and64 auxiliary-sign cases. These are
source/algebra controls, not complete accepting witnesses.


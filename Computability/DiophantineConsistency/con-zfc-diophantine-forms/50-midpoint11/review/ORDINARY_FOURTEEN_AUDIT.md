# Independent review of the ordinary-strong fourteen-variable equation

The reviewed construction has fourteen strictly positive coordinates and
uses the common native compiler abbreviations, but deletes h. Put

```
U=4q^4, r=k-R-1,
Dstar=U*b0+H*(U*gamma-r),
Astrong=Delta*(f^2-1), I=i*c^2,
V=c*(T*f-1)-R*f^2.
```

Its sum of four squares is

```
(Dstar^2-U^2*(1+Delta*c^2))^2
+(I^2-Astrong)^2
+(Astrong*(V^2-y^2)+y^2-1)^2
+(N0*Nt-1)^2.
```

Here `N0=tau^2-ell*(ell+k)` and Nt is the inherited unshifted transport
factor. The provided literal circuit was inspected; the ordinary-strong
equation replaces the normalized strong equation and eliminates the
otherwise necessary extra multiplication by Delta in the auxiliary factor.

## Noncircular bootstrap

At a positive root all four residuals vanish. The negative Pell obstruction
for consecutive products forces N0=1 from N0*Nt=1, hence Nt=1. The weak
compiler bounds give q>=16, 3q<R<q^4-2, X>=q, Y>=q^3, E=XY>=q^4,
k>=2, c>kY, a=E+Y, and H=4a+3<5a.

The scaled main equation makes g=Dstar/U a rational square root of the
integer 1+Delta*c^2, hence an integer. Its sign is positive because

```
g=b0+H*gamma-H*r/U
 >b0-H*k/U
 >a*k*(Y-5/U)>0.
```

Thus c=psi_A(p), g=chi_A(p), where A=a+2 and p>=2. Integrality also gives
U|Hr. The first Pell norm gives k=2psi_P0(n), P0=2EY+1, n>=1.
Since P0>A and c>k, monotonicity gives p>n.

The recurrence yields k=2n modulo 4EY, and U divides 4EY. The same
gcd computation as for the eleven-variable equation gives
gcd(U,H) in {1,3}. Therefore, with mu=U/gcd(U,H),

```
2n=R+1 modulo mu,  mu>=4q^4/3>R+1.
```

Writing 2n=R+1+j*mu, positivity forces j>=0. Consequently n>=25 and
p>=26. This supplies the essential bound for the ordinary-strong lemma:

```
c=psi_A(p)>=A^(p-1)>A*(A^2-1)^2=A*Delta^2.
```

Also c>2p, and c>=psi_A(2)=2A>2R.

## Ordinary-strong rank interface

Section 4 of the inherited `ORDINARY_BLANK_PROOF.md` was inspected.
Under exactly the proved bound c>A*Delta^2, the equation

```
(i*c^2)^2=Delta*(f^2-1)
```

gives |f|=chi_A(m), p|m, c|m, m>=c>2p, and
I=Delta*psi_A(m). Its proof uses strong divisibility at the fundamental
integer-coordinate Pell unit; it does not cancel Delta without proving
the rank assertion. In particular it proves c^2|(f^2-1), the needed
auxiliary residue fact.

The auxiliary equation is now I^2*V^2-(I^2-1)*y^2=1. The inherited
odd-index argument gives its index j0 congruent to +/-p modulo m and
to +/-R modulo c. With 0<p,R<c/2 this forces p=R. Since n<p, the
earlier nonnegative j must be zero: 2n=R+1. It follows that r is divisible
by 4EY, and hence by both E and U. The original h=r/E is positive.
The unscaled gamma reconstructed from g=b0+H*gamma_old is integral and
positive, because g>(a+1)c and c>X.

This reconstructs the complete inherited ordinary-strong compiler source
without using the deleted index equation as an assumption.

## Completeness

Start with a canonical normalized compiler witness and replace its strong
coordinate by i_ordinary=Delta*i_normalized, as in the inherited source.
The canonical rank identity gives r divisible by 4EY. Choose the new
positive coordinate gamma=gamma_old+r/U. Then Dstar=U*g and all four
residuals vanish. Both the divisibility and positive coordinate change
are proved, rather than inferred from a formal substitution.

## Conclusion and scope

No local mathematical defect was found in the ordinary-strong upgrade.
It has the same existence property as the inherited positive compiler
and therefore the same stated consistency equivalence. The exact
degree-56/79-operation claim has a separate literal circuit audit.
The proof here checks the new reduction and the precise rank-lemma
hypotheses; it is not a new formal-kernel certificate of the native
compiler or K215 calibration.

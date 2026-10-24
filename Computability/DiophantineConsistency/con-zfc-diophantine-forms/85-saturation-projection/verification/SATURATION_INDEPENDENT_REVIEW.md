# Independent mathematical review of the saturated Pell construction

Reviewed component: `research-frontier/saturation/PROOF.md`, its literal
polynomial tables, and the defining lines in `discover_radical.py`.
Reviewed source snapshot: ProveIt
`c1a102936aca437e9999530a0111e6ddab56dc6d`.

## Conclusion

The new unbounded Pell representation and both outer-norm arguments are
mathematically sound under the explicitly retained source/ratio/compiler
interfaces. I found no missing sign, divisibility, or rational-integrality
case in the new reduction. The two final exact degrees agree with an
independent recomputation of the cancellation-resolved degree formula.
This review does not certify the inherited native compiler or create an
end-to-end proof-assistant or object-language ZFC derivation.

One small presentation clarification was requested from the component author:
when the radical table is defined in the four independent indeterminates
`A,C,i,Z`, explicitly impose `J=4A-5`. The code does this correctly; the
generic theorem of Section 1 had allowed an independent J. The strict
positivity of P at the shift origin is also justified by its actual positive
constant, 15,915,642,730,652.

## 1. Saturating one factor of D

Write delta=A^2-1, D=1+delta C^2 and
F=1+delta D (i J C^2)^2. All factors are positive on the specified domain.
For Lambda=CD+1-A, G=A+F Lambda and H=C+F(B+j0 C), direct reduction gives

```
F == G == I == 1 mod D,
I == D mod F.
```

Thus gcd(D,F)=gcd(D,I)=gcd(F,I)=1. No assumption that D, F or I is prime
is present. Their square product forces each to be a square. If d^2=D,
then F=1+delta(i J C^2 d)^2 is precisely a positive Pell norm. The inserted
d is an integer recovered in the proof, not an uncharged variable in the
polynomial.

The inequality i J C^2 d >= 9A^2 > psi_A(3) is valid because C>B>1,
J>=A, and d>=A. Consequently its index m is greater than 3 before an
index-separation theorem is used.

For the rank step, let C=psi_A(s). Strong divisibility gives s|m, write
m=s u, and use the binomial expansion of
(chi_A(s)+psi_A(s)*sqrt(delta))^u. Modulo C^3 its second coordinate is
u chi_A(s)^(u-1) C. Since gcd(chi_A(s),C)=1, the assumed C^2|psi_A(m)
implies C|u and hence C|m. This reasoning covers even C; no hidden oddness
assumption is necessary.

Reduction of the recurrences modulo sqrt(F)=chi_A(m), followed by the
index-separation lemma, gives s=+/-t modulo 2m. For confirmation, the exact
external statement was read at
https://arxiv.org/html/2609.01594v1, Lemma 2.2: its Lucas parameter is 2A,
and v_m(2A)/2=chi_A(m). Its parameter and m>3 conditions are met here.
The component's added elementary proof was also checked: modulo
x=chi_A(m), psi_A(t+2m)=-psi_A(t) and psi_A(2m-t)=psi_A(t). Thus indices
fold to signed values psi_A(r), 0<=r<=m. Since A>=3 (already forced by
1<B<A), the Pell identity gives x>2 psi_A(m), so congruence of the signed
folded values implies integer equality and hence equal folded indices.
This proves the precise needed separation without relying on the external
general integral lemma.

Modulo C, G=1 and H=B. Therefore t=B modulo C. Together with C|m this
gives s=+/-B modulo C. The bound psi_A(s)>=A s for s>=2 and B<A implies
0<s+B<C, excluding the negative branch and any nonzero multiple in the
positive branch. Thus s=B.

## 2. Completeness is constructive and cofinal

Choose a positive period of the determinant-one Pell recurrence matrix
modulo J*d*C^2. Its corresponding psi value is divisible by that modulus;
division supplies the positive integer i and makes F a square. This is a
finite-group argument over a specified positive modulus, with no inference
from numerical evidence.

Next choose a period T of the G-recurrence modulo F. The progression
t=B+kTC simultaneously preserves t modulo T and modulo C, without a
coprimality requirement between T and C. The quotient
(psi_G(t)-C)/F is integral and congruent to B modulo C because F=1 modulo C.
It tends to infinity, so j0 is eventually a nonnegative integer. This
supplies the exact H required by the certificate. The period argument
establishes the claimed unbounded availability of witnesses.

The shorter transport i_new=d*i_old also checks exactly: it turns the new
one-D norm into the old D^2 norm and preserves F, G, H and I. It is used
only on actual old certificates where d is already integral.

## 3. Positivity precedes square recovery

For the cheap majorant T=A D e0 and V1=TGH, the identities

```
T^2-DF = D(D e0^2-1),
V1^2-DFI = (T^2-DF)(GH)^2 + DF(H^2-1)
```

are exact and strictly positive. They hold before assuming a final zero.
The companion defect V0^2-a0=K^2-1 is likewise positive. E0 is positive,
so Omega=Jm cannot vanish at a final zero. Factoring the real two-root
norm then forces m>0 for every choice of root signs, since both strict
majorants dominate the possible negative roots.

Only after m>0 is known is the source margin used. In particular it gives
C>K, and A^2>P. Thus DFI>C^2 A^4>K^2 P^2>a0. This strict inequality rules
out a zero rational sum of the two signed square roots. For nonzero rational
x=r0+r1, the formula 2x r0=x^2+a0-a1 makes both roots rational. A rational
square root of an integer is integral. The divisibility J|Q follows only
after this integral-root recovery. There is no circular use of the Pell
certificate to establish its own ambient range.

In the scaled-radical variant, sigma=1024 C^5 i is a positive integer.
After recovering an integral root r1 of sigma^2 DFI, the quotient r1/sigma
is rational with integer square DFI, so it is itself integral. No assertion
that sigma divides every arbitrary root is taken as an unproved shortcut.

For completeness, F>D and sigma>=1024 ensure the radical majorant exceeds
2D. The cheap majorant does also. Together with the inherited bound
W1^2+Q/J<2D, this makes the constructed n a strictly positive integer.

## 4. Exact radical certificate and degree accounting

The delivered shifted P table has 6,650 nonzero coefficients, all positive,
with constant 15,915,642,730,652. The shifted corrected defect has 36,309
nonzero coefficients, all positive, with constant
32,237,226,735,615,909,648. Consequently both inequalities are strict at
the boundary A=3,C=i=Z=1 as well as throughout the required region. The
uncorrected defect is not used as a majorant.

I independently inspected the weighted leaders of the delivered unshifted
tables at weights (18097,1,1,8799):

```
Pplus: degree 334575, unique leader 2^20 A^18 C^24 i^6 Z;
defect: degree 343404, unique leader 2^41 A^18 C^48 i^12 Z^2.
```

The outer algebraic identity is correct. Writing
B=E0^2-2 E0 Omega(V0+V1)+Omega^2(delta0+delta1), it reads

```
F9 = B^2 + 4 Omega^2 V0 V1 B
     + 4 Omega^4(delta0 V1^2 + a0 delta1).
```

For the cheap construction, B^2 has unique highest degree 1,628,768.
For the radical construction the four displayed summands have degrees
1,049,688; 1,103,950; 1,095,122; and 832,466, respectively. The second is
uniquely highest with positive leading coefficient. The exact degree is
therefore 1,103,950. These comparisons do not incorrectly treat the
negative leading coefficient of Omega as positive: Omega appears squared
in the dominant terms.

## Verification scope

This was an independent review of the unbounded arguments and defining
identities, with small direct inspection of the finite coefficient tables.
It did not repeat optional large discovery calculations or claim that
finite tests prove the semantic source-to-refutation bridge. The existing
source interfaces and their formalization limitations remain explicit.

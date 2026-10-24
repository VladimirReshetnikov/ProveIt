# Independent review: strong-root transfer into a positive transport gap

Date: 23 October 2026. Source/comparison revision:
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` of ProveIt.

This review was performed independently of the construction author and
builder. It is an internal AI-assisted mathematical and finite algebraic
review, not external peer review, a new Lean/Rocq certificate, or an
exported object-language ZFC derivation.

## Conclusion

The twelve-positive-variable construction in `section.tex` has a sound
existence-equivalence proof relative to exactly its stated inherited
normalized source, native coefficient adapter, and K215 calibration.
Its exact degree is 84 and its literal evaluator has 103 live binary
operations. The thirteen-positive companion has exact degree 30 and
94 operations. The two signed-root possibilities, the nonzero denominator,
and positivity of the inverse coordinate are all covered. No mathematical
gap or disagreement between the delivered circuit and specification was
found in this review.

The twelve-variable comparison to package 61 is degree 118/104 operations
to degree 84/103 operations, with the same number of positive unknowns.
The thirteen-variable comparison is degree 34/93 to degree 30/94, a
degree/cost tradeoff. Neither comparison proves global minimality.

## 1. Weighted transport carrier

The generalized multiplier is W=1+(q-1)h_* with h_*>0. Its essential
properties are W>0 and W=1 modulo q-1. For

    M=q^3(q-1),
    Bt=(q K0+X)C-qF,
    Z=M(ell+k+r)+(q-1)Y-q^3 W Bt,

the equation Z^2=M^2(ell(ell+k)+1) first makes Z/M an integer. Reduction
modulo q^3 and q-1 then gives q^3|Y and (q-1)|Bt, respectively. No
coprimality assertion about W beyond its displayed congruence is needed.

Writing s=Y/q^3 and t=Bt/(q-1), one obtains
tau=ell+k+r+s-Wt. The elementary bound |tau|<ell+k proves t>0 and
Bt>0. Because qK0+X>0 and F>0, it follows that C>0. Thus all native
packing bounds used later are established before rank recovery and before
q|X is known.

For completeness, h_*>=k makes the canonical choice
r=Wt+tau-ell-k-s positive, since t>=q, tau>ell and s<k give
r>qW-2k>0. The stronger multiplier h_*=ikc used by the twelve-variable
construction also satisfies this premise.

## 2. Adaptive main carrier, checked independently

The main carrier uses S=4qY, U=qS=4q^2Y, v=k-R-1 and

    Dstar=U(X+ac)+H(U gamma+SX-v).

With positive X supplied directly, the numerator is positive without
assuming X>=q: v<k and c>kY give Dstar>Uac-Hk, and UaY>H. The monic
square therefore yields a positive integer main root D=Dstar/U.

The first and main Pell norms give indices n0,p with n0<p. The boundary
n0=1 is impossible, since it would force k=2, eta=zeta=1 and
c=2Y+1<psi_(a+2)(2). Thus n0>=2, k>8XY^2 and
c>8XY^3>=8q^9>2R. The standard growth bound gives c>2p. These are
sufficient for the normalized strong-rank and signed auxiliary-index
lemmas of package 61; the older ordinary strong-rank size condition is
not being silently invoked. The conclusion is p=R.

The congruence calculation keeps the possible factor 3. Because
J=3j+1 and beta=1 modulo 3, q=2 modulo 3. After q^3|Y has been
established, gcd(q,H)=1 and

    g=gcd(H,U)=gcd(H,S)=gcd(H,Y) in {1,3}.

Integrality of Dstar/U implies U/g|SX-v, hence S/g|v. The first-Pell
congruence k=2n0 modulo 4XY^2 and S/g>R+1 force 2n0=R+1 because
1<=n0<p=R. Consequently v is a positive multiple of 4XY^2, and U|v
since U divides that modulus. Returning to the stronger congruence gives
q|gX, hence q|X. Thus the order of recovery has no circular use of
either q|X or the index quotient.

The restored w=X/q and h=v/(XY) are positive integers. The main root
identity, D>(a+1)c and c>X prove gamma_old=gamma+w-v/U>0. The already
positive transport numerator restores a positive shifted transport
quotient. These deductions give every source coordinate required by the
inherited normalized source interface.

Canonical completeness is also valid: v/U>=XY/q^2=wY/q>w, so
gamma=gamma_old-w+v/U>0. This argument does not require an additional
unproved promise that gamma_old>w.

## 3. The new norm and its signed roots

The following estimates hold on every positive input, not merely on a
zero of the proposed polynomial. Let

    A0rad=ell(ell+k)+1,
    Df=1+Delta I^2,
    L=(a+2)I,
    I=ic^2.

Since ell<ac and k<c,

    ell(ell+k)<a(a+1)c^2<Delta i^2 c^4.

Thus Df>A0rad>0. Also L^2-Df=I^2-1>0, since c>=3 and I>1.

For Zbar=Z0+ML, the new residual is

    N=(Zbar^2-M^2(Df+A0rad))^2-4M^4 Df A0rad.

If N=0 and Zbar=0, then M^4(Df-A0rad)^2=0, contradicting the strict
bound. Hence the denominator in

    f_star=(Zbar^2+M^2(Df-A0rad))/(2M Zbar)

is nonzero. The exact alternative norm identity gives f_star^2=Df.
A rational square root of an integer is integral, so f_star is a
nonzero integer. Furthermore ((Zbar-M f_star)/M)^2=A0rad; that
rational root is therefore also integral.

Set f=|f_star| for the normalized strong equation, but set
r=n+L-f_star for the first carrier. This distinction is necessary when
Zbar<0. Because L>|f_star|, r is a positive integer in both cases.
All the other strong-root occurrences are through f^2 only, so changing
to its positive absolute value there does not affect any residual. The
first carrier is exactly Z=Zbar-M f_star. The weighted-carrier lemma
therefore applies with no unsupported square-class or sign assumption.

## 4. Positivity in the inverse construction

For canonical source witnesses choose the positive strong root f and the
fresh auxiliary witnesses promised by package 61. Use h_*=ikc. The first
carrier gives r>qW-2k. The square-root approximation error satisfies

    0<L-f=(I^2-1)/(L+f)<I/a=ic^2/a<ikc,

because c=kY+eta<k(Y+1)<=ka. Moreover

    qW-2k-ikc = q+[q(q-1)-1]ikc-2k > 0

for q>=16 and ic>=3. Thus n=r-L+f is a strictly positive integer.
The resulting Zbar=M(tau+f) makes N vanish exactly. The adaptive main
carrier and the auxiliary equation remain zero. This completes the
reverse existence implication without a stronger congruence on the
auxiliary ordinate or a new coefficient tuple.

## 5. Independent degree audit

Degrees below count only the supplied unknowns, treating fixed ports as
degree zero. For the twelve-variable equation,

    deg M=4, deg I=5, deg L=7, deg Df=14,
    deg A0rad=8, deg Z0=10.

The exact cancellation identity is

    Zbar^2-M^2(Df+A0rad)
      =Z0^2+2ML Z0-M^2(1-I^2+A0rad).

Only the middle term reaches degree 21. The norm tail has degree 38,
so N has degree at most 42 and its unique top form is the square of
that degree-21 term. Writing q0=3 beta j, k0=eta+zeta and

    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F,

gives

    in_42(N)=4q0^16 i^4 k0^8 X^2 Y^8 Bt0^2,
    in_84(P12)=16q0^32 i^8 k0^16 X^4 Y^16 Bt0^4.

The auxiliary residual has degree at most 37 because its coefficient
and V each have degree 18, and its uncancelled product with u has
degree 37. The main residual has degree at most 13: writing
B=UX+H(U gamma+SX-v), its exact cancellation is

    A1=2Uac B+B^2-U^2 Hc^2-U^2.

Here deg B<=6 and deg(Uac)=7. Thus neither other squared residual
can contribute at degree 84. The coefficient of
j^32 i^8 eta^16 X^8 Y^16 alpha^4 is exactly 16(3 beta)^32>0.

For the thirteen-variable equation, writing Z=M ell+T0 gives

    A0=2M ell T0+T0^2-M^2 ell k-M^2,

where deg T0<=7. Thus its degree is at most 15. The main, auxiliary
and strong residual bounds are 13,13,14. The top coefficient
[j^16 eta^4 X^4 Y^4 alpha^2]P13=4(3 beta)^16>0 proves exact
degree 30. Both lower certificates are independent of the values of
the other three fixed ports and survive the authentic specialization.

## 6. Independent finite audit and scope

`independent_audit.py` was authored separately from `build.py` and the
construction's verifier. It uses a separate standard-library sparse
integer ring in `independent_ring.py`. It checks 46 exact named-register
contracts for the twelve-variable DAG and 42 for the thirteen-variable
DAG. Every anonymous gate is evaluated between those exact contracts,
and the final sum of squares is checked in independent residual variables.
This compositional check binds the complete literal circuits to the
mathematical specification without exponentially expanding the final
polynomial. It also checks the generic two-root identity, the center
cancellation, both displayed top forms and their selected coefficients,
gate/input liveness, and operation counts. The receipt is
`INDEPENDENT_AUDIT.json`.

The independently counted operations are 60 multiplications, 27
additions and 16 subtractions for P12, and 53,24,17 for P13, giving
103 and 94. These checks certify finite data and algebra. They do not
establish the unbounded existence theorem by a bounded search. The fixed
compact-tuple binding and its reconstruction belong to the construction's
separate coefficient audit; no claim of a second independent native
compiler proof is made here.

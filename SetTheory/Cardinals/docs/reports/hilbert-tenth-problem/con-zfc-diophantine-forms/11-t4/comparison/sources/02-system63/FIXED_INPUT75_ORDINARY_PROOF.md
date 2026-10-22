# Ordinary strong square: a75-gate polynomial of degree101

This is an optional lower-degree construction using the same fixed
program numerals and the same16 strictly positive unknowns as
`FIXED_INPUT73_PROOF.md`. Arithmetic input1 still means normalized
machine raw input2. No compiler constant, machine, or acceptance
predicate changes.

The complete polynomial has **75=41M+34A gates and exact degree101**.
The simpler seven-equation system has **63=34M+29A gates**, the same
count as the normalized system, but its maximum equation degree is
**28 rather than60**. Its literal sum of squared residuals costs
**83=41M+42A gates** and has exact degree56.

## 1. Exact changed equations

Keep q,X,Y,E,k,c,a,H,Delta,D,C,R,V,L, and all sixteen positive
coordinates from the73-gate construction. Define

    I=i*c^2,
    A0=Delta*(f^2-1),
    Na0=A0*(V^2-y^2)+y^2,
    Ns0=1+I^2-A0.

The other factors N0,N1,Nk,Nt,M are unchanged. The new polynomial is

    P75=N0*N1*Na0*Nk*Nt*Ns0*M-1.                  (1)

Equivalently, use the seven equations

    N0=N1=Na0=Nk=Nt=1,
    I^2=A0,
    q-F-Z-alpha=C.                               (2)

The ordinary strong equation is the original raw75 equation
(ic^2)^2=Delta*(f^2-1), not the normalized strengthening
f^2-Delta*(ic^2)^2=1. The distinction matters: this construction does
not assume that Delta divides the supplied i.

## 2. All norm factors are positive units

At a zero of(1), every displayed factor is an integer unit. M is
positive, so M=1 and the old budget consequences hold:

    q=W0+F+2Z+alpha,
    C=Z+W0>0, C<q, F+Z<q, W0<q.

Delta=(a+2)^2-1 is0 or3 modulo4. Since f^2 is0 or1 modulo4,

    A0=Delta*(f^2-1) is0 or1 modulo4.

Therefore Ns0=1+I^2-A0 can never be3 modulo4, and hence Ns0=1.
Also Na0 modulo4 is y^2 if A0=0 modulo4, and V^2 if A0=1 modulo4;
it too cannot be-1. The negative-Pell descent for N0 and the ordinary
modulo4 argument for N1 are unchanged. Consequently

    N0=N1=Na0=Ns0=1,
    Nk=epsilon, Nt=nu, epsilon,nu in{-1,1}, epsilon*nu=1,
    A0=I^2>0.                                     (3)

No sign of the index or transport factor has been assumed.

## 3. Bootstrap before auxiliary positivity

We must not reuse the normalized-source bound f>c^2. Instead establish
the main Pell index first, without using V.

The same admissible-mask estimates give

    (2q-1)(q^2-1)<R<q^4-q^3,
    E>=q^4>R+2, a>R+2, q>=16.

Put A=a+2 and P0=2XY^2+1. From N0=1 there is n>=1 with
k=2psi_P0(n). The index unit gives2n=R+epsilon modulo E and hence
n>=(R-1)/2>=24. From N1=1 there is p>=1 with
c=psi_A(p), D=chi_A(p). Since P0>A and c>k, p>n. Therefore

    c>A*Delta^2, c>2p, c>2R.                      (4)

This is exactly the bootstrap used by the repository's generic
strong-rank theorem and is independent of V, the input bridge,
or an already decoded computation.

The ordinary strong equality in(3) now implies

    f^2=1+i^2*c^4/Delta,
    f>c^2/sqrt(Delta)>c^2/A>2c.

Here c>A*Delta^2>2A and sqrt(Delta)<A. Since c>Delta+1 and f>2c,
also f^2>Delta+c. As R<a<Delta,

    A0-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.           (5)

These inequalities replace the normalized source's direct f>c^2
estimate and avoid assuming the rank conclusion prematurely.

## 4. Positivity and integrality of the omitted auxiliary coordinates

The auxiliary equation is

    A0*V^2-(A0-1)*y^2=1.

For v=|V|>1 it implies v>=2A0-1, by the same elementary gap argument
as in the73-gate note. Since T>0,
V=c(Tf-1)-Rf^2>-Rf^2-c>-A0 by(5). Thus V cannot be negative with
|V|>1. V=0,1,-1 are excluded by V=-c modulo f, with2<c<f/2.
Therefore V>1. The same norm then implies y>V, a useful fact for
the nonnegative quadratic-gate lift.

Apply the repository's generic strong-rank lemma to

    c=psi_A(p)>A*Delta^2,
    I=ic^2>0,
    I^2=Delta*(f^2-1).

It gives an index m with

    f=chi_A(m), p divides m, c divides m,
    I=Delta*psi_A(m), m>=c>2p.                    (6)

In particular

    f^2-1=Delta*psi_A(m)^2=ic^2*psi_A(m),

so **c^2 divides f^2-1**. This is the missing integrality fact; it
does not follow merely by dividing the original strong equality
without the rank theorem.

Define

    o=cT-Rf,
    j=Tf-1-R*(f^2-1)/c.

Both are integers. They satisfy

    of-c=V, jc=V+R.

Since V,R,c,f are positive, o,j>0. Thus the full positive auxiliary
relations V=of-c=jc-R are restored.

The signed auxiliary step-down lemma now gives p=R. It uses exactly
the positive o,j, the rank conclusions(6), and0<p,R<c/2.
For the no-wrap argument write2n=R+epsilon+vE, v>=0. If v>=1,
then2n>=R-1+E>2R+1>2p, contradicting n<p=R. Thus E>R+2 suffices;
the unavailable asymmetric estimate E>2(R+2) is not used.
Now2n=R+epsilon, and epsilon=-1 would
give p=2n+1 and contradict the strict ratio kY<c<k(Y+1).
Thus epsilon=nu=1. This proves that(1) implies(2); the reverse
implication is immediate.

## 5. Restoring a raw75 solution and proving completeness

The lower Pell ratio and projected recurrence recover X=2^R exactly
as in the73-gate construction. Thus q=2^ell and R>3ell, so
w_raw=X/q^3>0. The fixed endpoint and budget give

    q-C=(q-W0+F+alpha)/2>W0/2>=2d.

Restore alpha_raw=q-C-2d>0 and z_raw=t-1+wC>0. Recover the deleted
input Pell variables at u=2d+b<R using the same explicit formulas in
section4 of `FIXED_INPUT73_PROOF.md`. The difference is that now
**i_raw=i**: equation(2) already has the raw ordinary strong square.
Together with o,j above, all nineteen raw75 equations hold. The
same fixed-program compiler theorem therefore proves acceptance
at raw input2, and hence the intended K215 halting predicate.

For completeness it is enough to use the already proved73-gate
construction. Given one of its positive zeros, retain every coordinate
except replace i_normalized by

    i_ordinary=Delta*i_normalized.

At a normalized zero,
f^2-1=Delta*i_normalized^2*c^4. Hence

    A0=Delta*(f^2-1)
       =Delta^2*i_normalized^2*c^4
       =(i_ordinary*c^2)^2.

The auxiliary coefficient is unchanged, every other factor is
unchanged, and the ordinary strong factor is1. The new tuple is
strictly positive and satisfies(1)-(2). No divisibility of arbitrary
ordinary witnesses by Delta is asserted in the converse direction.

## 6. Literal source count

The existing f-square is retained. Replace the normalized four-row
strong block, costing3M+1A, by these six rows, costing3M+3A:

    f2_minus_one=f^2-1
    A0=Delta*f2_minus_one
    I=i*c^2
    I2=I*I
    ordinary_strong_sum=I2+1
    Ns0=ordinary_strong_sum-A0.

Use A0 as the existing auxiliary coefficient and subtract1 in the
final polynomial. Every other row is unchanged. The complete cost
therefore increases from73 to75, with the same41 multiplications.

For the seven-equation system compare I2=A0 directly. The last two
rows are unnecessary, giving63 gates,34M+29A. All gates, unknowns,
and fixed ports are live. A generic sum of squared residuals adds
seven residual subtractions, seven squares and six additions:
63+20=83 operations, or41M+42A.

## 7. Exact degree101 and degree56

Put Q=(B-1)J, k0=eta+zeta, T2=wZ-tQ, W1=Q-F-2Z-alpha.
The new auxiliary coefficient A0 has degree14, with leading form
w^2*s^2*Q^8*f^2. V has degree7, with leader k0*s*Q^3*T*f.
Thus Na0 has degree28 and leader

    k0^2*w^2*s^4*Q^14*T^2*f^4.

The ordinary strong factor has degree22 and leader
i^2*k0^4*s^4*Q^12. The full factor degrees are

    22,18,28,7,2,22,2,

and the full leading homogeneous form is

    8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4 T2 W1^2.

The monomial

    J^58 h gamma i^2 eta^9 w^7 s^16 t T^2 f^4

has coefficient-8(B-1)^58, nonzero uniformly for B>1. The exact
degree is therefore101. The final subtraction of1 is irrelevant.

The seven system residual degrees are22,18,28,7,2,22,1.
Only the auxiliary residual reaches28, so its squared leading
form proves that the sum of squares has exact degree56. This is
a substantive lower-degree option, without additional unknowns
or a larger comparison-system source.

## 8. Independent review and executable evidence

`verify_fixed_input_ordinary.py` first replays the normalized source
validation, including authentication of the upstream F84 Git blob.
It reconstructs the literal six-row replacement and the system's
dead-code pruning, checks all gates and supplied ports for liveness,
verifies64 signed full-source identities under i_o=Delta*i_n, and
executes the complete polynomials over exact integer coefficient
arrays. The factor degrees, full degree101 leader, and degree56
SOS leader agree with the proofs above. Normal and python-O
executions pass.

An independent review in `k215_notes/REVIEW_ORDINARY_STRONG75.md`
checks the unit signs, proof order, rank/divisibility step, literal
source change, operation ledgers, and exact degree calculation.
As with the73-gate construction, these arithmetic checks are not
an end-to-end Lean/Rocq formalization of the universal compiler,
and no global minimum claim is made.


# Positive packed indices are sound for the unresolved86 candidate

Every positive zero of the [weakened86 candidate](complete75_weakened_bound86_candidate.md)
with **computed packed index R>0** has the correct ordinary input under
the unchanged complete75 compiler contract. This removes the earlier
requirement alpha>Z from this branch. The literal86=48M+38A circuit,
its19 positive supplied coordinates and exact degree203 are unchanged.

This is **not a universal86 bound**: the circuit does not impose R>0.
Its remaining possible false-input zeros have R<0; R=0 is impossible.
The [checker](complete75_weakened86_positive_index.py) and
[receipt](complete75_weakened86_positive_index.json) audit the exact
original-source restoration and the new boundary arguments. The best
established75-certificate/87-polynomial bounds remain unchanged.

The [subsequent index-gap theorem](complete75_weakened86_index_gap.md)
proves p odd globally and, on the remaining R<0,mu>0 branch, excludes
p=2n-1 and requires n<p<=2n-3; zero wrap requires E<3p. These further
necessary conditions still leave the86 candidate unresolved.

The later [gap-three exclusion](complete75_weakened86_gap_three.md)
strengthens the same R<0,mu>0 branch to n<p<=2n-5. It does not settle
larger odd gaps or mu<0; the source and theorem below are unchanged.

## 1. Definitions and signs available at any candidate zero

Retain every fixed compiler hypothesis of
[coupled88](complete75_coupled_index_linear88.md), including

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 mod4, MF=4 mod8, popcount(MC)+popcount(MF)=d.

The candidate computes

    q=(B-1)J+1, X=wq^3, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A=a+2, Delta=A^2-1, H=4a+3,
    gamma=rho+sigma, D=X+ac+gamma*H,
    C=q-F-alpha-2d*x, W=C-Z,
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H,
    G=q(q-F)-Z,
    R=G(q^2-1)+(MC+q(MF+B-1))J.

Here A is a mathematical parameter; the literal register `A` holds
Delta. The program input offset b is positive and less than B. All
supplied coordinates, including F,Z,rho,sigma and both ratio slacks,
are strictly positive. Computed C,W,R,mu may initially have either sign.

The five norm factors of the normalized candidate are+1 at any zero:
the four main/first/input/auxiliary exclusions and the normalized strong
exclusion are precisely those of the parent proofs. Write the other
three factors as

    Nk=k-R-hE=epsilon,
    L=V-jc+k-hE=lambda, V=of-c,
    Nt=(K0+X)C+(q-F)-zplus*(q-1)=nu,
    epsilon,lambda,nu in {1,-1}, epsilon*lambda*nu=1.

Weak transport gives C>=0: if C<=-1 its first term is less than-1,
and q-F-zplus(q-1)<=0. Consequently F<q and C<q. The normalized
strong factor restores the full strong equation by setting

    i_old=Delta*i>0, T=i_old*c^2,
    T^2=Delta(f^2-1).

The auxiliary coefficient is exactly T^2 at these zeros. No weakened
rank hypothesis or omitted ratio is introduced.

## 2. The sharper positive-index packing interval

Put M=q^2-1 and

    S=Z+qF-1,
    TC=MC*J+1, TF=MF*J-1, Tmask=TC+q*TF.

The exact identity, valid on arbitrary assignments, is

    R=(q^2-S)M+Tmask.                                 (1)

The unchanged mask size/congruence conditions and J>0 imply

    3<=TC<q, 3<=TF<q-2,
    3q+3<=Tmask<M.                                    (2)

In particular R is never zero, since its remainder Tmask modulo M
lies strictly between0 and M. Also

    R>0 iff S<=q^2.                                   (3)

Assume R>0 for the rest of Sections2--4. Since S>=q, we obtain

    q<=S<=q^2,
    1<=Z<=q^2-q+1<q^2,
    3q+1<=R-2<R+2<q^4.                               (4)

For the upper bound use S>=q and Tmask<=q^2-2 in(1), giving
R+2<=q^4-q^3+q<q^4. Unlike the old stronger bound, (4) allows
S=q^2 and G=-1. Positivity of G is unnecessary: at that boundary
R=Tmask is still positive and satisfies every stated range bound.

The common scales give E>=q^6>2(R+2) and a>R+2. From the index
unit and h>=1, k>R+2, whence c>kY>2(R+2). These are all the
outer estimates needed in the coupled sign argument.

## 3. Coupled signs, including the formerly excluded boundary

The first norm's positive-root classification gives

    k=2*psi_P(n), P=2XY^2+1,
    2n=R+epsilon mod E, n>=(R-1)/2.

The main norm gives c=psi_A(p), D=chi_A(p), and monotonicity gives
p>n. Thus the retained strong-rank theorem applies, exactly as in
coupled88: c>A*Delta^2, c>2p, and there is a positive auxiliary
index m with f=chi_A(m), c divides m and m>=c>2p. In particular
V=of-c>0. The coupled linear unit is

    V=jc-(R+epsilon-lambda).

Both this target and p lie strictly between0 and c/2. The generic
odd-index congruence and signed step-down argument therefore gives
p=R+epsilon-lambda. The bounds in(4) identify the first-index
representative as 2n=R+epsilon. If lambda=-1, then p=2n+1;
Pell duplication gives c>k(Y+1), contradicting the retained upper
ratio. Hence

    lambda=1, nu=epsilon, p=R+epsilon-1.               (5)

All equations of the complete half-binomial kernel now hold at index
p, and (4) supplies 3q+1<=p<q^4 for either sign. Its conclusions
include q=2^t, X=2^p and popcount(p)>=3t+2. The repunit then types
q=B^N and J=1+B+...+B^(N-1), with t=dN.

If epsilon=-1, define

    Tminus=MC*J-1+q*(MF*J-1),
    p=R-2=(q^2-S)(q^2-1)+Tminus.

The unchanged mask congruences give 0<Tminus<q^2-1 and
popcount(Tminus)=t+1. When S<q^2, the same inverse-packing bound
used in coupled88 gives popcount(p)<=3t+1, a contradiction.
The new boundary S=q^2 is even simpler: p=Tminus, so its population
is t+1, again a contradiction. Therefore epsilon=nu=lambda=1.

This proof uses the complete kernel only after restoring its actual
positive coordinates and shifted index. It does not apply the kernel
to a negative R or assume Boolean typing while excluding a sign.

## 4. Restore the weaker101 interface directly

All eight candidate factors are now1. Nt=1 implies C>0 and zplus>=2.
Indeed zplus=1 would give (K0+X)C=F, impossible because C is a
positive integer and X>q>F.

Restore the positive supplied coordinates of
[signed projection101](complete75_signed_projection_elimination101.md) by

    alpha_101=F+alpha, r_101=R, z_101=zplus-1,
    i_101=Delta*i, tau_101=XY^2*k+tau_gap.

Keep every other supplied coordinate unchanged. The101 definition
C=q-alpha_101-2d*x is exactly the candidate's C; W=C-Z is unchanged.
The packing equation is(1), and all other retained101 equations follow
from the restored units and definitions. Every supplied101 coordinate
is strictly positive. In particular its root tau is positive, and
its packed-index coordinate is positive by the branch assumption.

The101 theorem proves the computed input root and omitted input gap
positive, recovers W=2^u and restores the entire original universal
source. It therefore proves the correct ordinary input here. There is
no need to make alpha_87=alpha-Z positive, or to turn this tuple into
one of the more restrictive87 tuples.

The exact original nineteen-residual audit uses the same map. All
definitional residuals vanish identically on arbitrary assignments.
Writing r_j for the historical nineteen residuals, the other identities
include

    N0=1-r5, N1=1+r11, N2=1+r17,
    Nk=1+r8, Nt=1+r2, L=1+r8-r14,
    r12=Delta*(1-Nstrong),
    Naux=1+r13-T^2*r14*(U+V), U=jc-R.

Thus factors equal to1 restore every original residual, after the101
proof supplies the omitted positive domains. The source does not divide
by Delta or add a comparison to the candidate circuit.

## 5. Global restrictions without assuming R positive

There is useful information even in the remaining branch. Let

    E_A(j)=chi_A(j)-a*psi_A(j).

Its initial values are1,2, its recurrence is the Pell recurrence, and
E_A(j)=2^j modulo H. Since the computed main root gives
E_A(p)=X+gamma*H and 0<X<H, X is the least positive representative
of2^p modulo H. In particular

    2^p>=X>=q^3>=4096, so p>=12.                     (6)

This argument does not use the first-index equation, any bound on R,
or a power-of-two conclusion for q. Standard Pell growth now gives
c>A*Delta^2 and c>2p globally. The full strong-rank theorem and
V>0 therefore hold globally as well. The same auxiliary residue
argument supplies the congruence

    R+epsilon-lambda=+p or-p modulo c,                (7)

but it cannot identify the representative without an additional bound.

There is also a global restriction involving the first Pell index n.
The first norm gives k=2*psi_P(n), with P=2XY^2+1 and n>=1.
The retained ratio definitions give

    kY<c<k(Y+1).

Since X,Y>=q^3>=4096, we have P>A>Y+1 and 2A^2-1>P.
Monotonicity of psi in its parameter gives psi_A(n)<c. The exact
duplication identity gives the opposite endpoint bound

    psi_A(2n)=2A*psi_(2A^2-1)(n)
             >2(Y+1)*psi_P(n)=k(Y+1)>c.

Thus strict monotonicity in the index proves **n<p<2n**, independently
of R and of the input root's sign. This does not identify either index
with the computed packed index.

The input norm has mu nonzero. If mu>0, classify kappa=psi_A(v)
and mu=chi_A(v). Then

    E_A(v)=C-Z+rho*H<q+rho*H<X+gamma*H=E_A(p).

Strict increase gives v<p. Also Z=C+rho*H-E_A(v)<E_A(p)<2c;
the last inequality follows from D<Ac, since c>1. Consequently,
writing K=q(q-F)(q^2-1)+(MC+q(MF+B-1))J, we have

    0<K<q^4, R=K-(q^2-1)Z.

The lower endpoint can be made strict enough to exclude both signs at
the largest possible wrap. Put M=q^2-1 and c_-=psi_A(p-1). The Pell
identity D=Ac-c_- gives E_A(p)=2c-c_-, so

    2c-Z=c_-+X+sigma*H+E_A(v)-C>c_->p.

Here X>C, E_A(v)>0, and c_->p follows from p>=12 and A>=2;
for example c_->=(2A-1)^(p-2)>p. Since M>=255, K>0 and
epsilon-lambda>=-2, this gives

    R+epsilon-lambda+2Mc=K+M(2c-Z)+epsilon-lambda>p,
    p-2Mc<R+epsilon-lambda<c/2.

For the upper bound use c>A^11 and A>q^6, which dominate q^4+2.
Together with(7), this confines the target to

    R+epsilon-lambda=s*p-j*c,
    s in {1,-1}, 0<=j<=2(q^2-1)-1.                  (8)

Indeed j<0 would give a target at least c-p>c/2, while j>=2M
would give a target at most p-2Mc. The endpoint j=2M is therefore
excluded for both signs. This remains a finite range of possible
multiples of c for each q, not a recovery of the intended index.

If mu<0, put -mu=chi_A(v), kappa=psi_A(v). Then instead

    Z=C+rho*H+chi_A(v)+a*psi_A(v),                    (9)

and the argument v<p is unavailable. This branch has not been removed.
Equations(6)--(9) are necessary restrictions, not full candidate solutions.

## 6. Exact remaining gap and verification limits

By(1)--(3), the only remaining region is

    R<0 iff S>q^2,
    Z>=q(q-F)+2>q-F>alpha, W=C-Z<0.

The candidate may or may not have false-input zeros there. The old
negative-index outer fixtures still do not satisfy all native norms.
Neither they nor the present branch restrictions settle full soundness.
Adding R>0 as an external condition is not an86-operation universal
polynomial construction; the cost/domain of enforcing it remains paid.

The receipt checks512 full original-source factor/output identities,
256 signed, with the new positive101 slack map. It checks the widened
untyped packing interval, including its G=-1 boundary and cases where
alpha-Z<=0; the new typed negative-sign boundary; and exact Pell
recurrence, rank-size and signed-input-root inequalities. These are
algebraic and partial-interface checks. No complete enormous positive
Pell zero or false-input zero is materialized. The conditional soundness
theorem is the proof above, not an inference from the finite fixtures.

The follow-up checks evaluate432 pairs of endpoint recurrences for
n<p<2n and exclude7,128 tested main indices outside that open interval.
Separate432 exact main/input Pell fixtures retain the actual mask and
scale formulas;108 also retain the input index congruence. They give
2,592 strict wrap endpoint checks, including both signs and all three
possible values of epsilon-lambda. They do not assert the first/auxiliary
norms, transport or complete candidate polynomial vanishes.

```sh
python3 complete75_weakened86_positive_index.py
```

Author receipt generation and fresh default replay pass. Independent full
proof/source review and fresh default replay pass without findings,
including the global p>=12 rank argument, positive-root wrap interval,
positive101 restoration and S=q^2 boundary. That review separately checks
192 original-source factor/full-output identities,96 signed, and108
positive-input-root wrap-bound fixtures. Those are partial algebraic
fixtures, not complete candidate zeros. All five local links resolve.
A second independent conceptual review confirms the stated branch
arguments and leaves the same negative-index gap unresolved.

These reviews concern the original positive-index theorem and its
earlier non-strict wrap bound. The added global n<p<2n argument,
strict endpoint exclusion and their new recurrence checks received a
separate full diff proof/source review and fresh default replay from the
root reviewer; all passed without findings. The updated author writer
and fresh default replay also pass, with the literal candidate source
hash unchanged. These new checks retain the partial-fixture scope above.

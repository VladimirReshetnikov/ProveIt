# Start-only norm elimination: 14 positive unknowns

## Result and exact scope

The authentic four Start-only compiler coefficients beta=B-1, K, MC,
MFstar=MF_native+B-1 are those of the audited inputless compiler. They
may be the earlier input-erasing compiler or the new direct blank-tape
compiler, but the complete appropriate coefficient recipe and its
semantic correctness theorem are essential. Arbitrary integers satisfying
only mask bounds are not a replacement.

There is an explicit polynomial in 14 strictly positive unknowns with
75 binary operations (44 multiplications, 31 additions/subtractions) and
exact degree 293. An equivalent five-equation system has 69 operations
(40 multiplications, 29 additions/subtractions), maximum degree 244.
Its positive-solvability is equivalent to that of the audited Start-only
15-variable/67-operation polynomial, and hence to a finite ZFC refutation.
These are ordinary mathematical proofs, not new proof-assistant builds.
The improvement is fewer unknowns, not smaller arithmetic or degree.

## 1. Formula and circuit

The positive unknowns are J,F,alpha,z,h,i,T,s,w,tau,eta,zeta,y,gamma.
Retain the Start-only abbreviations

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H, Dmain=X+ac+gamma H,
    C=q-F-alpha,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MFstar)J,
    L=E(kY).

Put

    N1=tau^2-L(L+k), N2=Dmain^2-Delta c^2,
    NI=k-hE-R, NT=(K+w)C+q-F-z(q-1).

The new auxiliary expressions are

    Q=(Delta i c^2)^2,
    d=1+Delta i^2 c^4,
    b=c+Rd, u=cT,
    A=Q(du^2+b^2-y^2)+y^2-1,
    Bcross=2Qub,
    Hnorm=A^2-d Bcross^2.

The polynomial is

    P14=N1 N2 NI NT (Hnorm+1)-1.

The five-equation system is

    N1=N2=NI=NT=1, Hnorm=0.

All abbreviations are computed polynomials, not additional witnesses.
The literal circuit computes the last cross term as
4*(Q*d*u^2)*(Q*b^2), avoiding construction of Bcross. Both descriptions
are identical on every signed assignment. Circuit files are
start_only14_polynomial75.json and start_only14_system69.json.

## 2. Unit signs and the pre-Pell packing bounds

At a positive zero of P14, all five factors are integer units.
Bcross is even, so Hnorm+1 is A^2+1 modulo 4, and therefore cannot be -1.
Consequently Hnorm=0 and N1 N2 NI NT=1.

The consecutive-product negative Pell descent gives N1=1, since
L(L+k)=XY^2(XY^2+1)k^2. Also Delta is 0 or 3 modulo 4, excluding N2=-1.
Thus NI=NT=epsilon for epsilon in {-1,1}.

The original transport bootstrap applies unchanged. It first gives C>=0:
q-F-z(q-1)=1-F-(z-1)(q-1)<=0 and K+w>=2 exclude C<0.
Also q-F=C+alpha>0. Without any special treatment of C=0 one has

    q <= G=q(q-F)-C <= q^2-q,
    0<(MC+q MFstar)J<(q-1)(1+2q).

Therefore

    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    R>3q+1, q>=16,
    E>=q^4>R+2, a>R+2.

These weaker but adequate bounds avoid relying on a premature C>0.
They use the actual native mask bounds and the shifted MF convention.
In particular b=c+Rd>0, u=cT>0, and Bcross>0.

## 3. Exact integer-root reconstruction, with its sign left open

Define rational f=A/Bcross. Hnorm=0 gives f^2=d>1. A rational whose
square is an integer is an integer (reduce its fraction to coprime
numerator and denominator). Thus f is a nonzero integer.
Put V=uf-b. The exact identity

    Q V^2-(Q-1)y^2-1
      =A-Bcross f+Q u^2(f^2-d)

shows that the auxiliary norm is 1, while

    f^2-Delta i^2 c^4=1.

Since b=c+Rd and f^2=d, this V is precisely c(Tf-1)-Rf^2.
No positivity of f has been established or used. Replace f by |f| and
T by sign(f)T for the next proof step only. This preserves Tf, f^2 and
all equations. Now f>0 but T may be signed. It would be invalid to
invoke the old positive-auxiliary theorem at this point.

## 4. Signed auxiliary rank recovery

The needed local proof uses V only up to its sign. Here are its details.
Set A0=a+2, P0=2XY^2+1. The first and main positive Pell norms yield

    tau=chi_P0(n), k=2 psi_P0(n),
    Dmain=chi_A0(p), c=psi_A0(p), n,p>=1.

P0>A0 and c>k give p>n. Since P0=1 modulo E, the index unit gives
2n=R+epsilon modulo E. Because 0<R+epsilon<E,
n>=(R-1)/2>=24. Thus c>2p. The positive h and E>R+2 also give c>2R.

The normalized strong equation directly gives
f=chi_A0(m), psi_A0(m)=ic^2. Strong divisibility implies p|m; expansion
of (Dmain+c sqrt(Delta))^(m/p), modulo c^2, then gives c|(m/p).
Hence pc|m, in particular c|m and m>2p.

Let rho=Delta i c^2, so Q=rho^2. The auxiliary norm classifies its
absolute root as

    |rho V|=chi_rho(ell), y=psi_rho(ell).

Here rho>1 and V is nonzero. Divisibility of chi_rho(ell) by rho forces
ell odd. Write ell=2v+1. The integer quotient polynomials satisfy

    chi_Z(2v+1)=Z Q_v(Z^2),
    Q_v(-Delta)=(-1)^v psi_A0(ell),
    Q_v(0)=(-1)^v ell.

For a sign e in {-1,1}, V=e Q_v(rho^2). The two congruences

    V=-c modulo f, V=-R modulo c

hold for signed T. Since rho^2=-Delta modulo f, squaring the first
quotient congruence and using Pell doubling gives

    chi_A0(2ell)=chi_A0(2p) modulo chi_A0(m).

The inherited plus chi step-down lemma, with 0<2p<m, yields
ell=+p or -p modulo m, hence modulo c. The second congruence then
yields R=+p or -p modulo c. Since 0<R,p<c/2, necessarily p=R.
The sign e causes no problem: it is absorbed in the displayed plus/minus.

Writing 2n=R+epsilon+vE, v>=0, E>R+2 excludes v>=1 because n<p=R.
If epsilon=-1, then p=2n+1; duplication and
chi_A0(2)>P0, A0>Y+1 imply c>A0 k>k(Y+1), contradicting
kY<c<k(Y+1). Therefore epsilon=1 and 2n=R+1.
In particular NT=1 now excludes C=0, so C>0.

## 5. Power, binomial extraction and masks without an auxiliary sign

Set r=(R-1)/2. The first/main Pell ratio lower estimate, which involves
no auxiliary coordinate, gives

    c/(k/2)>(X+1)^(2r)/X^r,
    Y>X^r/3, a>X^(r+1)/3>2^R.

The main projection recurrence gives X=2^R modulo H=4a+3. Both positive
representatives are less than a, hence X=2^R. Thus q=2^t; R>3q>3t
restores q^3|X, so X and Y have the symmetric q^3 scales.

For clarity, do not invoke the full symmetric theorem here: it includes
positive auxiliary hypotheses not yet restored. Invoke only its ratio
calculation (pell_kernel_half_binomial42.md, Section 5), which depends
on the first norm, exact main index, ratio interval and scales, not on
V or T. It gives

    0<c/k - xi/2 < 16r/(X+1)<1/2,
    xi=(X+1)^(2r)/X^r=M+theta,
    M=binom(2r,r)+sum_{j=1}^r binom(2r,r+j)X^j,
    0<theta<1/4.

M is even. Since Y<c/k<Y+1, these estimates force Y=M/2.
The central-binomial valuation formula yields
v2(Y)=popcount(r)-1, hence popcount(R)>=3t+2.
No assumption R=3 modulo 4 or positive V has occurred in this argument.

The exact repunit then gives q=B^N. The original inverse-population
packing lemma gives the authentic shifted mask conditions

    (C-1) AND (MC J+1)=0,
    F AND (MF_native J-1)=0.

These type the Start-only word, with the origin Start and selector 1
forbidden. Since q=0 modulo4 and beta=-1 modulo4, J=1 modulo4;
MC=2 modulo4 therefore makes MC J+1=3 modulo4. The first mask
condition forces C-1=0 modulo4, so C=1 modulo4. In the literal R
formula this gives R=C+MC J=3 modulo4.
The unchanged transport equation restores a positive physical quotient
z_old=z-1+wC, so the compiler's synchronization and local-tableau theorem
already give an initialized halting computation. This is sufficient for
soundness of P14 without ever asserting positivity of the recovered f.

Alternatively, to map to a positive solution of the old P67, now regenerate
fresh auxiliary witnesses at the same q,R,X,Y,k,c,a,Dmain:

    m=2cR, f_new=chi_A0(m), i_new=psi_A0(m)/c^2,
    rho_new=Delta psi_A0(m),
    y_new=psi_rho_new(R), V_new=chi_rho_new(R)/rho_new,
    o_new=(V_new+c)/f_new,
    T_new=(o_new+R f_new)/c.

The binomial expansion of (Dmain+c sqrt(Delta))^(2c) proves c^2 divides
psi_A0(m). R=3 modulo 4 gives the two canonical minus congruences,
so o_new is a positive integer. For the remaining division,
f_new^2=1 modulo c and V_new=-R modulo c give

    f_new(o_new+R f_new)=V_new+c+R f_new^2=0 modulo c.

Since gcd(f_new,c)=1, c divides o_new+R f_new. Thus T_new is a
positive integer. These fresh coordinates satisfy exactly the old
normalized strong and auxiliary equations. This is an existence map,
not a bijection preserving the 14 supplied coordinates: i,T,y may change.

## 6. Converse and comparison-system equivalence

Every old positive P67 zero has all six factors at their positive values.
There f^2=d and the auxiliary equation expands to A=Bcross f. Hence
Hnorm=0. Delete f to obtain a P14 zero. This is the easy direction.

The preceding soundness argument also proves NI=NT=1 on every positive
P14 zero, so P14 and the five displayed comparisons have identical
positive zero sets. Combining both directions establishes the claimed
existence equivalence with P67 and the fixed machine's halting condition.

## 7. Exact degree, not only a propagated bound

Write Q0=beta J, k0=eta+zeta, and
T2=w(Q0-F-alpha)-zQ0. Leading homogeneous parts are

    a0=wsQ0^4, c0=k0sQ0^3,
    Delta0=w^2s^2Q0^8, R0=Q0^3(Q0-F).

The four retained factors have exact degrees 22,18,7,2 and product leader

    8h gamma k0^3 w^5 s^8 Q0^29 T2.

The main norm degree18 uses its cancellation
(Dmain)^2-(a^2+H)c^2=2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

Q,d,b,u have degrees46,34,38,6. The unique degree122 term of A is Qb^2.
The two terms of Hnorm have degrees244 and214, so Hnorm has degree244
and leader

    w^16 i^12 k0^24 s^40 Q0^148 (Q0-F)^4.

Consequently P14 has degree293 and nonzero leader

    8h gamma i^12 k0^27 w^21 s^48 Q0^177 (Q0-F)^4 T2.

For example the coefficient of
J^182 h gamma i^12 eta^27 w^21 s^48 z is -8 beta^182, nonzero for beta>0.
The system sum of squares therefore has degree488 (and can be evaluated
in 82 operations by adding four unit residuals, five squares and four sums).

## 8. Verification and imports

The newly authored build_start_only14.py reads only inert JSON, verifies
all circuit dependencies/liveness/counts, checks 200 exact signed local
norm identities and shared-field evaluations, and independently expands
three modular affine univariate specializations attaining all stated
factor degrees and total degree. It does not execute any received code.

The proof imports the same standard Pell classification, strong
 divisibility, signed chi step-down, ratio estimates, central-binomial
valuation, inverse-population lemma and Start-only compiler semantics as
the prior mathematical audit. The new contribution is the precise signed
root transfer and its order of use. No accepting full K215 witness is
materialized; none is asserted to exist. No global minimality is claimed.

## 9. Mixed-sign strengthening and 32 unrestricted integers

The fourteen-variable polynomial is also sound when only
J,F,alpha,z,i,s,w,eta,zeta must be positive, while h,T,tau,y,gamma are
arbitrary integers. Completeness follows immediately from the already
constructed all-positive solutions. The sign relaxations require proof:

1. The first norm classifies |tau|; tau cannot be zero. The first-index
   congruence gives n>=(R-1)/2>=24 without any h sign. Since n>=2,
   k=2psi_P0(n)>2n>=R+epsilon. Thus h=(k-R-epsilon)/E>0 is recovered
   before rank bounds need it.
2. Signed T is nonzero at every solution, even though the reconstruction
   denominator contains T. Indeed d>Delta+c and Delta>R imply

       Q-b=(Delta-R)d-Delta-c >= d-Delta-c > 0,
       1<b<Q.

   If T=0, u=0 and Hnorm=A^2=0, so
   Qb^2-(Q-1)y^2=1. For any integer y, this implies |y|>=b+1 and then
   b>=2Q-1, contradicting b<Q. Therefore Bcross=2Qub is nonzero.
   A/Bcross is a nonzero integer root exactly as before. Neither its
   sign nor T's sign is used in the squared auxiliary rank proof.
3. The auxiliary norm classifies |y|; y=0 would force QV^2=1 with Q>1,
   impossible. Thus the signed-y replacement is harmless.
4. With signed gamma, N2=1 classifies Dmain=sigma chi_A0(p), sigma=+/-1.
   Rank recovery uses |Dmain| and yields p=R as before. Let
   e_R=chi_A0(R)-a psi_A0(R). Modulo H,
   e_R=2^R and e_R(chi_A0(R)+a psi_A0(R))=1.
   If sigma=-1, the source projection gives

       2^R X=-1 modulo H.

   But the ratio lower bound gives a>X^(r+1)/3>2^R X, since
   X>=16 and r=(R-1)/2>=24 imply (X/4)^r>6.
   Therefore 0<2^R X+1<H, a contradiction. Hence Dmain is positive.
   Exact power recovery follows. The recurrence for e_n, starting1,2,
   gives e_R>2^R for R>=2, so gamma=(e_R-2^R)/H>0 as well.

For each of the nine positive coordinates substitute

    Pos(u,v,w)=1+u^2+v^2+w(w+1).

This is always positive on integers, and every positive integer occurs.
Indeed the three-square theorem represents 4(n-1)+1 as one odd square
and two even squares, giving n=1+u^2+v^2+w(w+1).
Retain the five signed coordinates unchanged. This yields one equation
in 9*3+5=32 unrestricted integer variables with the same existence
condition. The nine substitutions cost63 operations, so the literal
75-operation core gives138 operations in this representation.

With the nine positive coordinates assigned weight2 and the five signed
ones weight1, the exact factor degrees are44,35,13,4,488. Thus the
converted polynomial has exact degree584. The existing nonzero leading
form loses only the weights on h and gamma relative to double degree:
2*293-2=584. The integer-domain worker supplies a separate literal
expanded-substitution circuit and checks; this section records the
mathematical sign argument that licenses it.

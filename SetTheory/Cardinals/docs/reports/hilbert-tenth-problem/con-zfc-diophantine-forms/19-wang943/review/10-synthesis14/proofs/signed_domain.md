# Six signed coordinates for the fixed-blank 67-operation polynomial

Research note, 22 October 2026. This is an ordinary mathematical proof, not
a Lean/Rocq certificate. It adapts the signed-quotient proof in the pinned
native-stream-queue notes to the inputless polynomial, and adds the elementary
automatic-positivity argument for the index quotient h.

## Statement and exact scope

Let all compiler coefficients be an authentic fixed-blank coefficient slice,
with the same native masks and mask population conditions as package 06.
Let P67 and P68 have precisely the definitions in that package. Permit

    tau, y, w, h, f, T in Z,

and require the other nine supplied coordinates

    J, F, alpha, z, i, s, eta, zeta, gamma

to be strictly positive. Then every zero of either polynomial determines a
zero in the original all-positive domain by

    tau -> |tau|, y -> |y|, f -> |f|,
    T -> sign(f) T,

with every other coordinate unchanged. In particular the signed solution
set has the same existence projection as the positive solution set.
The proof establishes w>0, h>0, f!=0, y!=0, tau!=0 and fT>0.

Consequently substitute Pos(a,b,c)=1+a^2+b^2+c(c+1) for the other nine
variables and leave the six displayed variables unrestricted. This gives
an explicit equation over 33 unrestricted integer variables. Each positive
integer is represented by Pos, by the three-square theorem applied to
4n-3. Pos is always strictly positive for integer arguments.

P67 gives 130=66M+64A operations and degree 292. P68 gives 131=66M+65A
operations and degree 228. These figures charge all 63 substitution gates.

## 1. Algebraic normalization, then automatic positivity of w

Write A=a+2, Delta=A^2-1, S=Delta*i*c^2, so the auxiliary coefficient is
S^2. The scaled strong norm is Delta*f^2-S^2 = Delta*Ns, where

    Ns=f^2-Delta*i^2*c^4.

We first show Delta never vanishes in the partially signed domain. We have
q=(B-1)J+1>=B>=16, Y=sq^3>=q^3, and a=Y(wq+1). For integer w, either
w>=0 and a>=Y, or w<=-1 and a<=-Y(q-1). Thus a is neither -1 nor -3,
and indeed Delta=(a+1)(a+3)>0.

Cancel Delta in the polynomial equation. Every normalized factor is an
integer unit. In particular N1=D^2-Delta*c^2 is a unit. If w<=-1, then
X=wq<0, a<0, H=4a+3<0, and c=kY+eta>0. Since gamma>0,

    D=X+ac+gamma*H < ac <0,
    N1 > -H*c^2 >1,

a contradiction. If w=0, then X=0, a=Y, and

    N1=H(2ac*gamma+gamma^2*H-c^2),  H=4Y+3>1,

which is not a unit. Hence w>0. This argument uses no positivity of h,
f or T and no halting or compiler soundness conclusion.

Now the usual unit-sign arguments apply. Delta is 0 or 3 modulo 4,
so N1 and Ns cannot be -1. The auxiliary coefficient S^2 is a square,
so Naux is congruent to y^2 or V^2 modulo 4 and cannot be -1. The first
negative norm tau^2-U(U+1)k^2=-1, U=XY^2>1, is excluded by the standard
consecutive-product Pell descent. Thus all four norm factors equal +1.
The index and transport factors are epsilon and nu in {-1,1}, with
epsilon*nu=1. Ns=1 excludes f=0. The first norm excludes tau=0; Naux=1
and S>1 exclude y=0. Replace tau,y by their absolute values and replace
(f,T) by (|f|,sign(f)T). Every polynomial value is unchanged, since
the only f-consumers are f^2 and Tf. Henceforth f,tau,y are positive,
while T remains unrestricted.

For P68, exactly the same cancellation first gives Ns=1. Its substituted
coefficient Delta(f^2-1) then equals S^2, so P67 and P68 coincide at
these zeros. Thus it suffices to continue with P67.

## 2. Untyped bounds and automatic positivity of h

The transport factor is

    Nt=(K+w)C+1-F-(z-1)(q-1), C=q-F-alpha.

Since K+w>=2 and the last terms are nonpositive, Nt being a unit implies
C>=0. Thus 1<=F<=q-1. The existing elementary packing estimates give

    R>3q+3, R<q^4-2, E=XY>=q^4>R+2.

They use only C>=0 and the actual mask bounds. In particular 2<R-1.
The index unit says

    k=hE+R+epsilon.

Because k=eta+zeta>0, h<=-1 is impossible. If h=0, then k=R+epsilon
lies strictly between 2 and q^4. But the first positive Pell equation
classifies k=2 psi_P(n), P=2XY^2+1, n>=1. For n=1 this equals 2;
for n>=2 it is at least 4P=8XY^2+4>q^4. Both alternatives contradict
the displayed interval. Therefore h>0.

This Pell gap is the only extra step needed to permit signed h. It is
independent of the auxiliary quotient and of a decoded computation.

## 3. Signed auxiliary rank: recovering the main index

The first and main positive norms give

    tau=chi_P(n), k=2 psi_P(n), P=2XY^2+1,
    D=chi_A(p), c=psi_A(p).

Since P=1 modulo E and 0<R+epsilon<E,

    2n=R+epsilon+vE, v>=0.

P>A and c>k imply p>n>=(R-1)/2>=24. Pell growth gives c>2p.
The index equation and h>0 also imply c>kY>2R.

The normalized strong equation gives f=chi_A(m) and
psi_A(m)=i*c^2. Strong divisibility of psi implies p|m. Writing m=pj,
the Pell addition formula modulo c gives

    psi_A(pj)/c = j*D^(j-1) mod c.

Since gcd(D,c)=1 and the left side is divisible by c, c|j. Hence pc|m,
and in particular c|m and m>2p.

The auxiliary equation is

    S^2 V^2-(S^2-1)y^2=1, S=Delta*i*c^2>1.

It gives an odd index ell=2v0+1 and sign e in {-1,1} with

    |SV|=chi_S(ell), y=psi_S(ell), V=e*C_v0(S^2).

Here C_v0(U) is the integral polynomial chi_s(2v0+1)/s in U=s^2,
and its elementary identities are

    C_v0(0)=(-1)^v0*ell,
    C_v0(-Delta)=(-1)^v0*psi_A(ell).

The literal V=c(Tf-1)-Rf^2 gives, for any signed T,

    V=-c mod f, V=-R mod c.

Since S^2=-Delta mod f, square the first congruence and use
chi_A(2j)=1+2Delta*psi_A(j)^2 to obtain

    chi_A(2ell)=chi_A(2p) mod f.

The plus-sign Pell step-down gives 2ell=+/-2p mod 4m. One elementary
proof uses chi_A(j+2m)=-chi_A(j) mod f, reflects the remaining index
into [0,m], and uses 2chi_A(m-1)<f. A negative congruence cannot identify
two positive representatives whose sum is below f; a positive one forces
equality and therefore equality of indices. The index m itself gives
residue zero and is excluded. Thus ell=+/-p mod 2m, hence modulo c.
Since c divides S, the second congruence becomes

    e*(-1)^v0*ell=-R mod c.

Therefore R=+/-p mod c. Both R and p are strictly between 0 and c/2,
so p=R.

If v>=1 in 2n=R+epsilon+vE, then 2n>=R-1+E>2R, contradicting n<p=R.
Hence 2n=R+epsilon. If epsilon=-1, p=2n+1. Put Q=chi_A(2)>P;
Pell duplication gives psi_A(2n)=2A psi_Q(n)>=A k. Since A>Y+1,
c=psi_A(2n+1)>k(Y+1), contrary to c=kY+eta with 0<eta<k.
Thus epsilon=nu=+1, and Nt=1 now implies C>0.

## 4. Power, population and parity without a positive auxiliary root

At this point R=p is odd. Put r=(R-1)/2>=24. No sign of V is assumed.
The lower Pell ratio gives, with xi=(X+1)^(2r)/X^r,

    c/(k/2)>xi,
    Y>xi/2-1>X^r/3,
    a>X^(r+1)/3>2^R.

The projection recurrence chi_A(j)-a psi_A(j)=2^j mod H gives
X=2^R mod H. Both 0<X<a and 0<2^R<a<H, so X=2^R exactly.
Since q divides X, q=2^t. The repunit equation forces d|t and q=B^N.
Also R>3q implies q^3 divides X.

The exact half-binomial extraction depends only on this odd R, the ratio
interval, and the scales. For clarity, its proof does not use R=3 mod4.
The elementary estimates give

    0<c/k-xi/2<16r/(X+1)<1/2.

Expanding xi=M+theta, where

    M=binom(2r,r)+sum_{j=1}^r binom(2r,r+j)X^j,

gives 0<theta<1/4 and M even. Therefore M/2<c/k<M/2+1, forcing
Y=M/2. Thus v2(Y)=pc(r)-1, and q^3|Y implies

    pc(R)=pc(r)+1>=3t+2.

For the inputless source define

    S_word=C-1+qF,
    T_word=(MC*J+1)+q(MF_native*J-1).

The literal source gives R=(q^2-S_word)(q^2-1)+T_word. We have
0<S_word<q^2, and q=B^N gives pc(T_word)=t+2. The existing elementary
inverse-population lemma gives pc(R)<=3t+2, with equality exactly when
S_word AND T_word=0. Hence

    (C-1) AND (MC*J+1)=0.

Because MC=2 mod4 and J=1 mod4, this forces C=1 mod4. The literal
packing identity then gives R=C+MC*J=3 mod4. This conclusion uses the
native masks but no computation decoding and no positivity of T or V.

## 5. The two unsquared congruences restore T>0

The stronger step-down above gives

    ell=epsilon0*R+2m*z0, epsilon0 in {-1,1}, z0 in Z.

Write r=(R-1)/2. The elementary Pell identities and parity yield

    (-1)^v0*epsilon0=(-1)^(r+m*z0),
    psi_A(ell)=epsilon0*(-1)^z0*c mod f,
    ell=epsilon0*R mod c.

Substitute into BOTH unsquared congruences V=-c mod f and V=-R mod c:

    e*(-1)^(r+m*z0)*R=-R mod c,
    e*(-1)^(r+(m+1)*z0)*c=-c mod f.

Since c>2R and f>2c, each sign equals -1 as an ordinary integer.
Their quotient implies z0 even. Thus e*(-1)^r=-1. Section 4 gave
R=3 mod4, so r is odd and e=+1. Therefore V>0. Finally

    c*T*f=V+c+R*f^2>0

implies T>0, since c,f>0. This completes restoration of the positive
domain and allows the original positive-domain compiler theorem to apply.

## 6. Exact weighted degrees

Give weight two to J,F,alpha,z,i,s,eta,zeta,gamma, and weight one to
tau,y,w,h,f,T. Constants have weight zero. Put Q=(B-1)J and k0=eta+zeta.
Then deg(X)=3, deg(Y)=8, deg(E)=deg(a)=11, deg(c)=10, deg(Delta)=22,
deg(R)=8 and deg(V)=12. In the main norm the degree-42 terms cancel:

    N1=2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

Its exact weighted degree is 34. The six P67 factor degrees are
42,34,112,12,4,88; the P68 auxiliary factor has degree 48 instead of112.
The P67 leading form is

    8 Q^92 h gamma i^4 k0^13 w^13 s^26 T^2 f^2 z,

and the P68 leading form is

    8 Q^72 h gamma i^2 k0^9 w^11 s^20 T^2 f^4 z.

After the nine disjoint Pos substitutions the weight-two leaders become
their nonzero quadratic forms. Setting the second and third variables of
each Pos triple to zero reduces the top-degree substitution to
x_j -> u_j^2, which is injective on the polynomial ring. Thus the exact
degrees are 292 and228 uniformly for every authentic coefficient slice.

## Sources and limitations

Pinned repository commit: 3b201cdea32d2c816f5f3d20734051f25fd3ef14.

* Package 06, proofs/fixed_blank_67_proof.md: base polynomial, pretyping
  bounds, original positive domain and compiler equivalence.
* native-stream-queue/complete84_signed_w_charts_aristotle.md: signed-w
  argument, adapted verbatim in substance to the inputless source.
* native-stream-queue/complete84_signed_quotient_absorption.md: direct
  normalized rank and absolute-value auxiliary step-down.
* native-stream-queue/complete84_signed_quotient_soundness_scout.md:
  odd-index power/population proof and two-congruence sign recovery.
* The h argument and the combined 33-variable conversion are supplied
  in this note. No universal-operation-frontier or global optimality
  assertion is made. The signed-T source note is a mathematical scout;
  the required argument has been restated and checked above rather than
  being treated as a proof-assistant theorem.

# Ordinary strong norm with the Start-only auxiliary quotient

This note combines the ordinary strong norm of package 02 with the Start-only
compiler and the auxiliary quotient of package 06. It concerns the pinned
ProveIt commit `3b201cdea32d2c816f5f3d20734051f25fd3ef14`. The proof starts
from the `06-blank67` coefficient contract and applies equally to the
separately proved four-cell recipe, which satisfies the same arithmetic,
mask, and Start-only invariants. The primary coefficients are the four
ports of `data/four_cell_constants.json`, taken together; the four ports
of `06-blank67`, taken together, are a valid legacy alternative. Never
mix ports between the recipes. This is an ordinary mathematical proof,
not a new Lean or Rocq theorem. The compiler's ordinary correctness theorem
and the K215 calibration remain the same inherited dependencies.

## 1. Explicit construction

Use the fifteen positive variables

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Use the four fixed coefficients beta=B-1, K, MC, MFsrc from one complete
valid recipe as specified above, including the shifted convention
MFsrc=MF_native+B-1. Define

    q=beta*J+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y,
    A=a+2, H=4*a+3, Delta=a^2+H=A^2-1,
    D=X+a*c+gamma*H,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MFsrc)*J,
    L=E*k*Y,
    V=c*(T*f-1)-R*f^2,
    U=i*c^2,
    Kaux=Delta*(f^2-1).

The proposed system S consists of six equalities:

    tau^2-L*(L+k)=1,                         (S0)
    D^2-Delta*c^2=1,                         (S1)
    Kaux*(V^2-y^2)+y^2=1,                    (Sa)
    k-h*E-R=1,                               (Sk)
    (K+w)*C+(q-F)-z*(q-1)=1,                 (St)
    U^2=Kaux.                               (Ss)

Its literal evaluator has 61 binary operations (34 multiplications and
27 additions/subtractions); comparisons and register reuse are free under
the same convention as all eight preceding packages. The residual degrees
are 22,18,28,7,2,22, so the maximum degree is 28.

For the single product polynomial, write the first five left sides as
N0,N1,Na,Nk,Nt and put

    No=1+U^2-Kaux,
    P69=N0*N1*Na*Nk*Nt*No-1.

This polynomial has 69=39M+30A operations, fifteen positive unknowns, and
exact degree 99. The sum of the six squared residuals of S has
78=40M+38A operations and exact degree 56.

## 2. The only new difficulty: recover rank before the auxiliary sign

Package 06 uses f^2=1+Delta*i^2*c^4. It obtains f>2c and proves positivity
of V before invoking the strong-rank theorem. Replacing that equation by
(Ss) requires a changed proof order. Merely substituting the ordinary norm
in its old proof would leave a gap: the quotient (f^2-1)/c is not
manifestly integral before rank recovery.

The first and main Pell equations and the index factor already give the
large-main-index condition independently of the auxiliary norm. Thus rank
can be recovered first. The full lemma gives both p|m and c|m; the latter
was the conclusion emphasized in the later step-down argument. The
additional divisibility p|m makes (f^2-1)/c integral and enables the
quotient projection.

## 3. Unit signs and outer bounds for the product polynomial

At a positive zero of P69 all six integer factors are units. The
consecutive-product negative-Pell descent from package 06 gives N0=1.
The main discriminant Delta is 0 or 3 modulo 4, so N1 cannot be -1.

The ordinary strong factor No also cannot be -1 modulo 4, without using
any other equation. If Delta=0 mod4, No=1+U^2 mod4, which is 1 or 2.
If Delta=3 mod4, No=U^2+f^2 mod4, which is 0,1,or2. Consequently No=1
and Kaux=U^2 is a positive integer square. It follows that Na is congruent
modulo4 to y^2 or V^2, so Na cannot be -1 either. Therefore Na=1.

Write Nk=epsilon, Nt=nu, with epsilon,nu in {-1,1} and epsilon*nu=1.
Exactly as in package 06,

    (q-F)-z(q-1)=1-F-(z-1)(q-1)<=0.

If C<=-1, the transport factor is at most -(K+w)<=-2. Thus C>=0.
The exceptional C=0 boundary is retained here. Since q-F=C+alpha>0,

    1<=F<=q-1,
    q <= G=(q-1)(q-F)+alpha <= q^2-q,
    0 < (MC+q MFsrc)J < 2q^2-q-1.

The unchanged package-06 coefficient hypotheses imply

    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    R-2>3q+1,
    E>=q^4>R+2,
    a=E+Y>R+2.

These are the weaker valid Start-only bounds; no old fixed-input bound
R<q^4-q^3 is silently substituted.

## 4. Large c from the first, main, and index equations

Let chi_A(n),psi_A(n) denote the positive Pell sequences with discriminant
A^2-1. Set P=2XY^2+1. The first norm gives

    tau=chi_P(n), k=2psi_P(n), n>=1.

The main norm gives D=chi_A(p), c=psi_A(p), p>=1. Since P>A and c>k,
monotonicity implies p>n. Since P=1 modulo E,

    2n=R+epsilon modulo E.

Because 0<R+epsilon<E, one has n>=(R-1)/2>=24. Pell growth now yields

    c>A*Delta^2, c>2p, c>2R.                  (G)

The last inequality also follows directly from
k=R+epsilon+hE, h>=1, E>R+2, and c>kY. No positivity of V and no
auxiliary rank theorem has been used up to this point.

## 5. Ordinary strong-rank lemma, with its extra useful conclusion

The inherited lemma states that if

    c=psi_A(p)>A Delta^2,
    (i c^2)^2=Delta(f^2-1),

then for an integer m>0,

    f=chi_A(m), p|m, c|m, i c^2=Delta psi_A(m).      (RANK)

The following proof records that p|m is indeed part of the lemma, rather
than a new unproved strengthening. Write Delta=d0*s0^2 with d0>1
squarefree. Take the least positive integer-coefficient norm-one unit
F+y0 sqrt(d0). All positive integer-coefficient units are its powers.
For some e>=1,

    A=chi_F(e), s0=y0*S, S=psi_F(e),
    Delta=(F^2-1)S^2, psi_F(ep)=S*c.

The ordinary strong norm gives another positive unit, for some n>0, with

    f=chi_F(n), i c^2=(F^2-1)S psi_F(n).

Put T0=(F^2-1)S and g=gcd(n,ep). Strong divisibility of the Pell sequence
gives h0=gcd(psi_F(n),psi_F(ep))=psi_F(g). Since c^2|T0 psi_F(n),

    c*gcd(c,Delta)
      =gcd(c^2,T0 psi_F(ep)) | T0*h0,

so h0>=c/T0>=c/Delta. If g were a proper divisor of ep, then 2g<=ep
and Pell duplication would imply

    2 h0^2 < psi_F(2g) <= S c < A c.

But c>A Delta^2 and h0>=c/Delta contradict this inequality. Hence
ep|n, and writing n=em yields p|m and the first, second, and fourth
assertions of (RANK).

For c|m, write m=pt. Pell composition gives

    psi_A(pt)/c = t*chi_A(p)^(t-1) mod c.

Since c^2|Delta psi_A(m) and gcd(c,chi_A(p))=1, it follows that c|Delta t.
Also psi_A(p)=p A^(p-1) mod Delta and gcd(A,Delta)=1 give
gcd(c,Delta)=gcd(p,Delta). This gcd divides p, while
c/gcd(c,Delta) divides t. Thus c|pt=m.

Now use the previously underused conclusion p|m. Pell composition gives
c|psi_A(m), so

    c^2 | f^2-1=Delta psi_A(m)^2.              (DIV)

In particular the deleted coordinate j will be an integer.

## 6. Positivity and restoration of the auxiliary coordinates

The ordinary strong equation gives

    f^2=1+i^2*c^4/Delta.

Since c>A Delta^2, with A>=2 and Delta>=3, we have c>2A and c>Delta.
Thus f>2c, and f^2>Delta+c. Since R<a<Delta,

    Kaux-(R f^2+c)
      =(Delta-R)f^2-Delta-c
      >=f^2-Delta-c>0.                         (B)

The auxiliary equation is Kaux V^2-(Kaux-1)y^2=1. It excludes V=0.
For v=|V|>1, it gives

    v^2-1=(Kaux-1)(y^2-v^2),

and y>=v+1 implies v>=2Kaux-1. On the other hand T>0 gives
V>-(R f^2+c)>-Kaux. Hence V cannot be negative with |V|>1.
The congruence V=-c mod f, together with f>2c and c>2, excludes V=+/-1.
Therefore V>0.

Set

    o=cT-Rf,
    j=T f-R*(f^2-1)/c-1.

The quotient in this mathematical restoration map is integral by (DIV).
It is not an operation in the polynomial evaluator. The identities

    of=V+c>0, jc=V+R>0

give o,j>0 and V=of-c=jc-R. By (RANK), m>=c>2p. These are precisely
the positive-coordinate and rank hypotheses of the inherited signed
auxiliary step-down lemma. That lemma yields p=R.

Write 2n=R+epsilon+vE, with v>=0. If v>=1, E>R+2 gives n>R=p,
contrary to p>n. Thus 2n=R+epsilon. If epsilon=-1, then p=2n+1.
For Q=chi_A(2)>P, Pell duplication gives

    psi_A(2n)=2A psi_Q(n)>=A k,
    c=psi_A(2n+1)>A k>k(Y+1),

contrary to kY<c<k(Y+1). Therefore epsilon=1 and nu=1. Transport
with value+1 now excludes C=0, so C>0. All six equalities of S follow
from a positive zero of P69. The converse is immediate by multiplication.

## 7. Compiler and consistency consequences

After p=R, the retained asymmetric lower-ratio argument recovers X=2^R.
The repunit equation then gives q=B^N; the half-binomial/population
argument recovers the same two native masks; and the Start-only compiler
recovers a blank halting computation of K215. These steps are unchanged
from package 06 and use only hypotheses just recovered.

Conversely, take any positive zero of package 06's normalized P67. Keep
all coordinates except i, and define

    i_ordinary=Delta*i_normalized.

Then

    (i_ordinary c^2)^2
      =Delta^2 i_normalized^2 c^4
      =Delta(f^2-1).

The auxiliary coefficient is unchanged on that zero. Thus every one of
the six equations S holds. This proves completeness directly from the
existing Start-only construction. It is an existential equivalence, not
a claim that every ordinary tuple has i divisible by Delta.

Consequently, with the same explicit K215 coefficients, S, P69, and its
sum-of-squares polynomial have positive solutions exactly when K215
halts. Combining the inherited ordinary calibration with this ordinary
arithmetic proof gives, formalizably in ZFC,

    no positive solution <-> Con(ZFC).

The proof does not appeal to the soundness of Lean or Rocq inside ZFC.

## 8. Exact degrees and reproducible artifacts

Give each supplied variable degree one and each fixed coefficient degree
zero. Let Q=beta J, k0=eta+zeta, C1=Q-F-alpha. Then

    X_top=wQ, Y_top=sQ^3, E_top=w s Q^4,
    c_top=k0 s Q^3, a_top=E_top, Delta_top=a_top^2.

The factor leaders are

    N0: -k0^2 w^2 s^4 Q^14                         degree22
    N1: 8 gamma k0 w^2 s^3 Q^11                    degree18
    Na: k0^2 w^2 s^4 Q^14 T^2 f^4                 degree28
    Nk: -h w s Q^4                                degree7
    Nt: w C1-zQ                                   degree2
    No: i^2 k0^4 s^4 Q^12                         degree22.

For N1, use the exact cancellation identity with L0=X+gamma H:

    (ac+L0)^2-(a^2+H)c^2=2acL0+L0^2-Hc^2.

The full degree-99 leader of P69 is

    8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4 (w C1-zQ).

Its monomial J^56 h gamma i^2 eta^9 w^7 s^16 T^2 f^4 z has coefficient
-8 beta^56, which is nonzero for every valid compiler slice. The sum of
squares has unique highest residual Na-1 of degree28, so its exact
degree is56. This gives uniform degree proofs, not merely numerical
specializations.

`ordinary_start.py` derives all three complete source DAGs from the pinned
package-06 JSON, checks liveness and exact gate counts, verifies the factors
and SOS identity on 200 signed integer assignments, checks the ordinary
strong modulo-four obstruction exhaustively, and checks three full
univariate modular degree specializations. These checks support the local
algebra. They do not instantiate the enormous compiler coefficients or
prove any claim about whether K215 actually halts.

## 9. Relevant existing sources

- `06-blank67/proofs/fixed_blank_67_proof.md`: the Start-only construction,
  weak pretyping bounds, index sign recovery, and unchanged compiler step.
- `02-system63/PELL_INTERFACE_LEMMAS.md`: ordinary strong rank interface.
- `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`:
  the complete rank argument, explicitly concluding both p|m and c|m.
- `.../research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md`:
  quotient projection, auxiliary gap estimate, and normalized predecessor.
- `.../research-wip/native-stream-queue/complete75_reversed_auxiliary89.md`:
  signed auxiliary step-down theorem.

This combination differs from the old ordinary-strong system by retaining
the single quotient T in place of two supplied positive coordinates o,j.
The key is the proof order and the divisibility (DIV), not a new Pell rank
theorem.

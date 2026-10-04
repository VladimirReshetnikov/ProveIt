# Recovered proof: full positive collapse of the auxiliary square/product82

## Recovery and theorem

This file was reconstructed after the 2026-10-04 01:03 UTC filesystem
reset. It is a newly pinned proof, not a claim of byte identity with the
lost author proof. All eight restored upstream snapshots have been
rehash-verified against the previously authenticated pins. Historical
lost-release hashes are recorded separately and do not authenticate any
newly reconstructed file.

**Theorem.** Fix any genuine six-numeral compiler tuple inherited by
`complete82_auxiliary_square_product_chart`, and any positive ordinary
input x. Its complete polynomial has a strictly positive integer witness
tuple. In fact it has infinitely many such tuples. The fixed compiler
constants and x are never changed.

The source is frozen at commit
`6ce2dcaaf49d28de43ce9396a094643308fb0595`; the three author SHA256 pins are

- Python: 5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc
- JSON: 7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a
- Proof: 10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9

This is the **auxiliary square/product82**, distinct from Report41's
first-index-deleted82 and Report43's free-coefficient83. Here the first
index equation, its positive witness h, and S=i*Delta*c^2 are retained.
Applying the theorem to the genuine compiler of the empty computably
enumerable set establishes ordinary-input language failure of this
candidate. No new universal operation bound follows.

All divisions, exponentials and Pell coordinates in this proof define
existential witnesses; they are not additional free circuit operations.
The proof is symbolic. Neither upstream Python nor a saved arithmetic
schedule is executed, and no astronomical full witness is materialized.

## 1. Literal source and compiler contract

Write the genuine fixed ports as B−1,K,ell,b,MC,MF. Their unchanged
inherited recipe gives

    B=2^d, d=5^a, a>=1, ell=2d, K>0,
    b an odd power of5 with b>=5,
    MF=MF0+B−1, 0<MC,MF0<B−1, MC≡2 (mod4).

The last congruence is not an extra restriction. The baseline mask is
MC0=B−1−sum_(e in E,e!=1)(2^b)^e. The Start exponent0 contributes1,
whereas every positive exponent contributes a multiple of4, so MC0≡2.
The half-binomial mask correction subtracts2*(2^b)^e_* at a nonzero
ignored dummy exponent and preserves that residue. All other genuine
compiler conditions continue to hold because no fixed numeral is changed.

To avoid conflating the power a in d=5^a with a paid Pell quantity, use a0
for Y(X+1). The exact retained source meanings are

    q=(B−1)J+1, X=wq, Y=sq^3, E=XY,
    a0=Y(X+1), A=a0+2, Delta=A^2−1, H=4a0+3,
    k=eta+zeta, c=kY+eta, D=X+a0*c+(rho+sigma)H,
    C=q−F−Z−alpha−ell*x, W=C−Z,
    I=ell*x+b, kappa=I+delta*Delta,
    mu=W+a0*kappa+rho*H,
    G=q^2−qF−Z, Q=q^2−1, M=(MC+q*MF)J, R=GQ+M.

The five unchanged factors are

    Nfirst=tau^2−XY^2(XY^2+1)k^2,
    Nmain=D^2−Delta*c^2,
    Ninput=mu^2−Delta*kappa^2,
    Nindex=k−hE−R,
    Ntransport=(K+w)C+q−F−t_tr(q−1).

Let P5 be their product. The actual new supplied coordinates are
F_aux=`L16` and U_aux=`auxiliary_Tf`; the packing witness F is distinct.
The exact auxiliary expressions and output are

    S=i*Delta*c^2,
    V=c(U_aux−1)−R*F_aux,
    Na=S^2*V^2−(S^2−1)y_aux^2,
    Qs=F_aux−Delta*i^2*c^4,
    P82=Delta*(P5*Na*Qs−1).                       (1)

Indeed the retained strong factor is Delta*F_aux−S^2=Delta*Qs, and
all six product multiplications and the final subtraction of Delta
remain paid. Equation(1) is an all-value polynomial identity, not an
informal replacement of the finalizer by separate equations.

## 2. Radix and residues

Fix x>=1, I=ell*x+b and W=2^I. Choose r>=a large enough that

    t=5^r >=4 max(I,bit_length(K),61,16).

Then t>=625. Put

    q=2^t, N=5^(r−a), J=(q−1)/(B−1),
    Q=q^2−1, M=(MC+q*MF)J,
    m3=(MC+2MF) mod3 in {0,1,2}.

Here N is positive odd, q=B^N, and J is a positive integer. Since
t≡1 mod4, q≡2 mod5 and Q≡3 mod5. Since t≡1 or2 mod3,
q≡2 or4 mod7, and Q≡3 or1 mod7. Thus Q is a unit modulo5 and7.
Also

    M≡m3 (mod3), M≡2 (mod4).                    (2)

For mod3, B≡2 and the sum of N odd alternating powers of B is
J≡1, while q≡2. For mod4, B≡q≡0 and J≡1.

## 3. CRT branch when m3 is 2 or 1

Put epsilon=1 if m3=2 and epsilon=−1 if m3=1. Choose

    e=8 if K not≡1 (mod5), otherwise e=9,
    L=K+2^e, beta=Q(1+qL),
    Astar=Q*(q^2−q*(LW+1−epsilon))+M.

For e=8, 1+qL≡3+2K mod5, whose unique zero is K≡1.
At that exceptional K, e=9 makes 1+qL≡2 mod5. Therefore beta
is invertible modulo t=5^r. Choose the unique positive Z<=4t with

    Z≡1 (mod4),
    Astar−beta Z≡3e/2−epsilon (mod t),           (3)

where division by2 means modular inversion. These congruences have a
unique class modulo4t because4 and t are coprime. Define

    F=L(W+Z)+1−epsilon,
    alpha=q−F−2Z−W−ell*x,
    R=(q^2−Z−qF)Q+M=Astar−beta Z.               (4)

Positivity is proved in Section5. By(2), R≡3 mod4 and R≡m3 mod3.
Thus R≡11 mod12 when epsilon=1 and R≡7 mod12 when epsilon=−1.
Consequently

    u=(R+epsilon)/6, p=4u, n=3u, yexp=2u−1       (5)

are integers; u is even in the positive-sign branch and odd in the
negative-sign branch. From(3), using inverses of2 and3 modulo t,

    p≡e (mod t), 2n=R+epsilon.                  (6)

## 4. CRT branch when m3 is 0

Choose h0 in{1,...,12} such that e=5h0 makes

    1+q(K+2^e) nonzero modulo5 and modulo7.

Such h0 exists: modulo5, 2^(5h0)=2^h0 depends on h0 mod4 and at
most one of its four distinct values is forbidden. Modulo7, 2^(5h0)
has three distinct values depending on h0 mod3, with at most one
forbidden. CRT modulo12 gives at least(4−1)(3−1)=6 valid classes.
In particular5<=e<=60. Put

    epsilon=1, L=K+2^e, beta=Q(1+qL),
    Astar=Q*(q^2−qLW)+M, T=t/5.

Now beta is a unit modulo7 and modulo T. Choose the unique positive
Z<=28T satisfying

    Z≡1 (mod4),
    Astar−beta Z≡−1 (mod7),
    Astar−beta Z≡7h0−1 (mod T).                 (7)

The three moduli4,7,T are pairwise coprime. Define F,alpha,R by(4),
where epsilon=1. Then R≡−1 mod28. Therefore

    v=(R+1)/28, p=20v, n=14v, yexp=15v−1         (8)

are integers. Equation(7) implies28v≡7h0 mod T, hence4v≡h0 mod T,
and therefore20v≡5h0 mod5T. Thus again

    p≡e (mod t), 2n=R+epsilon.                  (9)

The condition R≡0 mod3 only forces v≡1 mod3 and causes no obstruction.

## 5. Uniform strict margins and actual packed R

In both branches1<=Z<=6t and1<=e<=60. Write U=2^(t/4) as a real
number for estimates. The choice of t gives W,K,2^e<=U. For t>=625,
13t<U: it holds at625 and U/t is increasing thereafter. Hence

    W+Z<2U, L<=2U,
    0<F<=4U^2+2,
    2Z+W+ell*x<=13t+U<2U.

Since U>4, 4U^2+2+2U<U^4=q. Thus alpha>0, F+Z<q, and all
four supplied outer witnesses J,F,Z,alpha are positive integers.
The latter inequality gives

    2q−1<=G=q^2−qF−Z<=q^2−q−1.

The genuine shifted bounds give0<M<(q−1)(1+2q): use MC<B−1,
MF<2(B−1) and J=(q−1)/(B−1). Consequently the actual source R obeys

    (2q−1)(q^2−1)<R<q^4−q^3.                   (10)

For the upper endpoint, expand
(q^2−q−1)(q^2−1)+(q−1)(1+2q)=q^4−q^3.
For q>=3 the lower endpoint exceeds q^3, so R>2^(3t)>100t.
Hence u>R/7>14t in Section3 and v>R/28>3t in Section4. In particular

    u>=3 or v>=2, p>I, p>t+e, yexp>=3t.         (11)

Define positive integers w=2^(p−t), s=2^(yexp−3t). The exact source
scalings now give X=wq=2^p and Y=sq^3=2^yexp.

## 6. Exact Pell resonance and both positive ratio witnesses

For A>=2 define integers chi_A(j),psi_A(j) by

    (A+sqrt(A^2−1))^j=chi_A(j)+psi_A(j)sqrt(A^2−1).

They obey the Pell recurrence and norm1. For j>=3 the elementary
recurrence bounds are

    (2A−1)^(j−1)<=psi_A(j)<(2A)^(j−1).           (12)

Induct on j using strict increase of psi; the upper bound becomes
strict at j=3. Define

    E=XY, a0=Y(X+1), A=a0+2, Delta=A^2−1,
    H=4a0+3, P=2XY^2+1,
    D=chi_A(p), c=psi_A(p),
    tau=chi_P(n), k=2psi_P(n).

The first/main norms are exactly1, because P^2−1=4XY^2(XY^2+1).
With L0=2XY and M0=4XY^2, both branches have the exact resonance

    L0^(p−1)=2Y*M0^(n−1).                       (13)

Equality of exponents is equivalent to
p(p−n)=(yexp+1)(2n−p): its value is4u^2 in the first branch and
120v^2 in the second. Furthermore

    2A−1=L0(1+1/X+3/(2XY)),
    2A=L0(1+1/X+2/(XY)),
    2P=M0(1+1/(2XY^2)), 2P−1>M0.

Equations(12)–(13) give c/(kY)>1, since its lower bound is the ratio
of the first perturbation to the third, raised respectively to p−1
and n−1; the numerator base is larger and p>n. For the upper bound,
let z=1/X+2/(XY)<2/X. Then(p−1)z<2p/2^p<1/2. Using

    (1+z)^j<=1/(1−jz)<1+2jz for0<jz<1/2,

we obtain

    0<c/k−Y<4pY/X
       =8u*2^(−2u)<1 in the first branch,
       =40v*2^(−5v)<1 in the second branch.      (14)

The final comparisons hold at u=3 and v=2 and decrease thereafter.
Thus eta=c−kY and zeta=k−eta are positive integers, restoring exactly
k=eta+zeta and c=kY+eta.

Because P≡1 mod E, the recurrence gives psi_P(n)≡n mod E.
Therefore h=(k−2n)/E is a positive integer: divisibility follows from
the congruence, positivity from psi_P(n)>n. Equations(6),(9) now give

    Nindex=k−hE−R=epsilon.                      (15)

The retained index equation has not been deleted or bypassed.

## 7. Shared main/input projection, with all quotients positive

Put z_j=chi_A(j)−a0*psi_A(j). It has z_0=1,z_1=2 and
z_(j+2)=2A z_(j+1)−z_j. The sequence2^j satisfies this recurrence
modulo H=4A−5, so z_j≡2^j mod H. Thus

    g_j=(z_j−2^j)/H

is an integer with g_0=g_1=0,g_2=1 and

    g_(j+2)=2A g_(j+1)−g_j+2^j.

Induction gives g_(j+1)>g_j>=0 for j>=1. By p>I>=3, the witnesses

    gamma=g_p, rho=g_I, sigma=g_p−g_I

are positive integers. Set kappa=psi_A(I),mu=chi_A(I). For odd I,
the binomial Pell expansion gives

    psi_A(I)≡I*A^(I−1)≡I (mod Delta),

since A^2≡1 mod Delta. Therefore delta=(kappa−I)/Delta is a positive
integer, as psi_A(I)>I. The shared source equations are exactly

    kappa=I+delta*Delta,
    mu=W+a0*kappa+rho H,
    D=X+a0*c+(rho+sigma)H,
    Ninput=mu^2−Delta*kappa^2=1.                 (16)

Here W is the actual paid value: (4) gives C=W+Z and C−Z=2^I.
No separate input exponent or unrelated second projection is substituted.

## 8. Transport and full auxiliary completion

As p≡e mod t and p>t+e, w=2^(p−t) satisfies w≡2^e mod(q−1) and
w>2^e. Hence

    t_tr=1+(W+Z)(w−2^e)/(q−1)

is a positive integer. Substitute C=W+Z,F=(K+2^e)C+1−epsilon:

    Ntransport=(K+w)C+q−F−t_tr(q−1)=epsilon.     (17)

The three norms first/main/input equal1 and the two remaining factors
both equal epsilon. Thus P5=1, including m3=1 where two signs are negative.

The actual R is positive and R≡3 mod4 in every branch. Set

    i=1, S=Delta*c^2, F_aux=Delta*c^4+1,
    V=chi_S(R)/S, y_aux=psi_S(R).

For R=2j+1 the standard odd-index polynomial identity reads

    chi_S(2j+1)=S Q_j(S^2),
    Q_0(T)=1, Q_1(T)=4T−3,
    Q_(j+2)(T)=(4T−2)Q_(j+1)(T)−Q_j(T),
    Q_j(0)=(-1)^j(2j+1).

It follows from the chi recurrence in steps of two; the constant term
follows by induction. Because R≡3 mod4, j is odd. Since c divides S,
V is a positive integer and V≡−R mod c. Also F_aux≡1 mod c. Thus

    U_aux=(V+R*F_aux)/c+1

is a positive integer, restoring the literal source relation
V=c(U_aux−1)−R*F_aux. Its Pell norm is Na=1, and Qs=1 by definition.
Equation(1) therefore gives the complete output P82=0.

This direct R-index extension makes no odd-c assumption. Indeed p is
even in both branches, and the recurrence modulo2 makes c even. Also
p even and R odd imply p!=R throughout. The old odd-c sector theorem
cannot be the justification here; the explicit congruence above is.

Additionally F_aux is nonsquare: since D^2−Delta*c^2=1 and c>1,

    (cD)^2−F_aux=c^2−1>0,
    F_aux−(cD−1)^2=c(2D−c)>0.

Thus F_aux lies strictly between consecutive squares. This supplements
the language failure theorem; it is not the only conclusion.

## 9. Domain and conclusion

The 18 supplied witnesses in exact source order are

    J,F,alpha,t_tr,F_aux,h,i,U_aux,s,w,
    tau,eta,zeta,y_aux,Z,delta,rho,sigma.

Every one has been defined as a strictly positive integer. All six fixed
ports and the given x are unchanged. Arbitrarily large r are available,
with unbounded J, proving infinitely many tuples per compiler/input.

The companion checker corroborates the theorem with bounded tests. It
compares every saved source row as data and authenticates the source
bytes; it never evaluates that schedule or runs upstream code. Large
outer tests stop at q,R,p,n,yexp and modular/exponent identities; only
small component tests materialize Pell integers. Diagnostic mask tuples
are not presented as actual compiled programs. The full unbounded
statement follows from this proof, and its specialization to the genuine
empty-set compiler yields the ordinary-input counterexample.

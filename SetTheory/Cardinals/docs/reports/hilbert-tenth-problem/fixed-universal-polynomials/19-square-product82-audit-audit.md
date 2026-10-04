# Independent audit of the full inherited compiler collapse of square/product82

## Verdict and recovery status

**PASS.** The frozen auxiliary-square/product82 chart has a strictly
positive 18-witness zero for every positive ordinary input and every
fixed numeral tuple produced by its unchanged genuine inherited compiler.
The construction has infinitely many such tuples at each input, even c,
main index p different from the actual packed R, and nonsquare F_aux.

This document and its independent checker were reconstructed after a
workspace replacement. They have new computed hashes. They are not
authenticated by the historical audit/checker hashes. The eight immutable
repository snapshots were recovered separately and their historical
source hashes match. Fresh normal and optimized checks are recorded in
this recovered packet; the pre-replacement verdict is not substituted
for fresh release evidence.

The result proves collapse of the inherited representation. The genuine
compiler for the empty computably enumerable set then accepts every
positive input in this candidate. It does not show that the same
polynomial could never support some different numeral compiler. It gives
no new universal gate bound and makes no priority claim. Report41's
first-index deletion and Report43's free-coefficient83 chart are different
objects and are not settled by this proof.

## Frozen source and genuine prerequisites

The primary reference is the [review at commit
6ce2dcaaf49d28de43ce9396a094643308fb0595](https://github.com/VladimirReshetnikov/ProveIt/blob/6ce2dcaaf49d28de43ce9396a094643308fb0595/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete82_auxiliary_square_product_chart.md).
Its adjacent Python, JSON and proof pins are respectively:

    5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc
    7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a
    10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9

The review's own hash is
02a12fd0426ad57b7c2bc822bc93266ed6511334e98cfb712cdd9f893d75722c.
The baseline76 recipe, changed75 compiler and retained84 interface imply

    B=2^d, d=5^a (a≥1), ell=2d, odd b≥3, K>0,
    MF=MF0+B−1, 0<MC,MF0<B−1, MC≡2 (mod4).

In fact the inherited radix bound 2^b≥16 and power-of-five choice give
b≥5. Merely being a power of five would not exclude b=1; this point
was clarified during the article review. Only odd b≥3 is needed here.

The MC residue follows directly: B−1≡3 mod4, the baseline Start
exponent contributes the unit 1, and every other subtracted radix power
vanishes mod4. The half-binomial change subtracts twice a nonzero dummy
radix power, again zero mod4. The MF shift is essential and has not
been dropped. No other restriction on a genuine compiler tuple changes;
the argument uses only these consequences of the full recipe.

## Literal source audit

The six fixed ports are Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF,
with values B−1,K,ell,b,MC,MF. The ordinary input is the prescribed x.
The witness names in the pinned source are

    Jrep,F,alpha,transport_quotient,L16,h,i,auxiliary_Tf,s,w,
    tau_root,eta,zeta,y_aux,Z,delta,rho,sigma.

They receive J,F,alpha,t_tr,F_aux,h_index,1,U_aux,s,w,tau,eta,zeta,
y_aux,Z,delta,rho,sigma in exactly that order.

I read the entire inert 82-row array. Its factor meanings are:

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    a0=Y(X+1), A=a0+2, H=4a0+3, Delta=A²−1,
    k=eta+zeta, c=kY+eta, D=X+a0*c+(rho+sigma)H,
    C=q−F−Z−alpha−ell*x, W=C−Z, I=ell*x+b,
    kappa=I+delta*Delta, mu=W+a0*kappa+rho*H,
    R=(q²−qF−Z)(q²−1)+(MC+qMF)J.

The five retained factors are

    tau²−XY²(XY²+1)k²,
    D²−Delta*c²,
    mu²−Delta*kappa²,
    k−h_index*E−R,
    (K+w)C+q−F−t_tr(q−1).

The auxiliary block is S=i*Delta*c², V=c(U_aux−1)−R*F_aux,
Na=S²V²−(S²−1)y_aux² and Ns=Delta*F_aux−S². With P5 the product
of the five retained factors, the actual seven-factor finalizer gives

    P82=Delta*(P5*Na*(F_aux−Delta*i²*c⁴)−1).

This is an all-value polynomial identity. In particular, the scaled
product is not replaced by an informal conjunction of positive units.
The source register A is Delta, R14 is D, R10a is c, r_lhs is the
computed R, and L16 is F_aux, distinct from the packing coordinate F.
All source definitions, including the first-index quotient and finalizer,
are retained. Only inert literal rows are compared by the checker.

## Independent verification of the outer construction

Fix x>0, I=ell*x+b, W=2^I. Choose t=5^r, r≥a, with
t≥4max(I,bit_length(K),61,16). Thus t≥625. Set q=2^t=B^N,
N=5^(r−a) odd, J=(q−1)/(B−1), Q=q²−1 and M=(MC+qMF)J.
Then q≡2 mod5, q∈{2,4} mod7, Q is invertible at 5 and 7,
M≡2 mod4 and M≡m3=(MC+2MF) mod3. The last congruence uses
the odd-length alternating repunit J≡1 mod3; J≡1 mod4 also holds.

For m3=2,1 take epsilon=1,−1 respectively. Set e=8 unless K≡1
mod5, when e=9, and L=K+2^e. Then beta=Q(1+qL) is invertible
mod t: the bracket is 2K+3 mod5 in the first choice, or 2 mod5
in the exceptional choice. Put Astar=Q[q²−q(LW+1−epsilon)]+M.
Choose Z≡1 mod4 and Astar−beta*Z≡3e/2−epsilon mod t, with
0<Z≤4t. The moduli are coprime and the inverses used are valid.
Now R=Astar−beta*Z is 3 mod4 and m3 mod3. Therefore

    u=(R+epsilon)/6, p=4u, n=3u, yexp=2u−1

are integers; u is even for epsilon=1 and odd for epsilon=−1.
The CRT relation gives p≡e mod t and 2n=R+epsilon.

For m3=0, take epsilon=1, choose h0∈{1,...,12}, e=5h0 so
1+q(K+2^e) is nonzero mod5 and mod7. Modulo5 the four h0 classes
mod4 give four distinct powers, at most one forbidden. Modulo7 the
three h0 classes mod3 give three distinct powers, at most one forbidden.
Hence at least six h0 exist by CRT modulo12. With L=K+2^e,
beta=Q(1+qL), Astar=Q(q²−qLW)+M and T=t/5, choose

    Z≡1 (mod4), R=Astar−beta*Z≡−1 (mod7),
    R≡7h0−1 (modT), 0<Z≤28T.

All required inverses exist and 4,7,T are pairwise coprime.
Then R≡−1 mod28 and

    v=(R+1)/28, p=20v, n=14v, yexp=15v−1

are integers. Since 28v≡7h0 modT, 4v≡h0 modT and multiplication
by5 gives p≡5h0=e mod t. Also 2n=R+1. No division modulo3 occurs;
the fixed zero residue only forces v≡1 mod3.

In either branch define F=L(W+Z)+1−epsilon and
alpha=q−F−2Z−W−ell*x. These restore C=W+Z and the actual affine
packed R, rather than just an abstract index. For U=2^(t/4), the
uniform inequalities W,K,2^e≤U, Z≤6t and 13t<U give

    F≤4U²+2, 2Z+W+ell*x<2U, 4U²+2+2U<U⁴=q.

Thus alpha>0 and F+Z<q. Also 2q−1≤G=q²−qF−Z≤q²−q−1 and
0<M<(q−1)(1+2q), from the genuine shifted-mask bounds. Consequently

    (2q−1)(q²−1)<R<q⁴−q³, and R>q³>100t.

These estimates ensure u≥3 or v≥2, p>I, p>t+e and yexp≥3t.
Therefore w=2^(p−t), s=2^(yexp−3t) are positive integral supplied
witnesses with the required X=wq and Y=sq³.

## Pell ratio, retained index and shared input

Set X=2^p,Y=2^yexp, E=XY, a0=Y(X+1), A=a0+2,
Delta=A²−1,H=4a0+3,P=2XY²+1. Take
(D,c)=(chi_A(p),psi_A(p)) and (tau,k)=(chi_P(n),2psi_P(n)).
The two actual norm factors are exactly one.

Both parameter families satisfy the exact resonance

    (2XY)^(p−1)=2Y(4XY²)^(n−1),

equivalent to p(p−n)=(yexp+1)(2n−p). The elementary bounds
(2A−1)^(j−1)≤psi_A(j)≤(2A)^(j−1), combined with p>n,
give c/(kY)>1. For the upper estimate z=(1+2/Y)/X<2/X and
(p−1)z<1/2, so c/(kY)<(1+z)^(p−1)<1+2(p−1)z<1+4p/X.
Hence 0<c/k−Y<4pY/X, equal to 8u*2^(−2u)<1 or
40v*2^(−5v)<1 at the established thresholds. Thus eta=c−kY and
zeta=k−eta are positive integers, with the exact source ratio meanings.

As P≡1 modE, psi_P(n)≡n modE. Therefore
h_index=(k−2n)/E is a positive integer, and its factor is epsilon.
This restores the retained first-index equation with its actual sign.

For z_j=chi_A(j)−a0*psi_A(j), the recurrence gives z_j≡2^j modH.
The quotients g_j=(z_j−2^j)/H have g0=g1=0,g2=1 and
g_(j+2)=2A*g_(j+1)−g_j+2^j. They strictly increase starting at j=1.
Define rho=g_I>0, sigma=g_p−g_I>0, kappa=psi_A(I), mu=chi_A(I).
For odd I≥3, the Pell binomial expansion gives
psi_A(I)≡I*A^(I−1)≡I modDelta. Thus
delta=(kappa−I)/Delta is a positive integer. These same rho/sigma
restore D=X+a0*c+(rho+sigma)H and mu=W+a0*kappa+rho*H, with the
actual paid W=2^I. The input norm is one and the ordinary x is unchanged.

## Matched signs and all-parity auxiliary completion

Since p≡e mod t and p>t+e, w≡2^e mod(q−1) with w>2^e.
Consequently t_tr=1+(W+Z)(w−2^e)/(q−1) is positive integral.
Direct substitution of F=(K+2^e)C+1−epsilon gives the actual transport
factor epsilon. Thus the five-factor product is 1, including m3=1
where the two negative factors cancel. No supplied witness is negative.

Set i=1,S=Delta*c²,F_aux=Delta*c⁴+1 and
V=chi_S(R)/S,y_aux=psi_S(R). For R=2j+1, the odd quotient identity
chi_S(R)=S*Q_j(S²) has Q_j(0)=(-1)^j(2j+1). Since R≡3 mod4,
j is odd, and c|S implies V≡−R modc. Also F_aux≡1 modc.
Hence U_aux=(V+R*F_aux)/c+1 is a positive integer and restores the
literal V. The auxiliary Pell norm gives Na=1, while
F_aux−Delta*i²*c⁴=1. The complete paid output is therefore zero.

The argument does not need odd c. In fact p is divisible by4, and
psi_A(p)≡p mod2 makes every constructed c even. Also R is odd, so
p≠R. This family lies outside the review's odd-c sector. Since
D²−Delta*c²=1 and c>1, the differences from the neighboring squares
are (cD)²−F_aux=c²−1>0 and F_aux−(cD−1)²=c(2D−c)>0.
Every supplied F_aux is nonsquare. This inverse failure is supplementary
to the stronger ordinary-input result.

All eighteen supplied values are positive integers, fixed numerals and
x are unchanged, and infinitely many r satisfy the size condition.
Their distinct unbounded J prove an infinite counterfamily at each input.
The genuine empty-set compiler specializes the theorem to false accepted
ordinary inputs; no toy masks are promoted to genuine compiler evidence.

## Fresh bounded corroboration and release boundary

The reconstructed checker is independent standard-library code. It
authenticates three source pins, checks the source interface and compares
19 critical rows as data. Its fresh evidence is 70 exponent-control
cases, 2,520 outer cases (840 per m3), 18 small exact Pell families,
five exact even-c auxiliary completions and 288 all-parity congruences.
The largest actual outer R has 12,500 bits. Large outer cases never
construct X=2^p or their enormous Pell coordinates. The small component
cases do not claim complete genuine compiler witnesses. The quantified
theorem rests on the proof above, not finite enumeration.

The checker deliberately writes receipt.json beside itself; release
replay should run it in a private temporary copy. Its default source path
is the sibling directory square-product82-counterfamily-recovered-20261004/source.
An explicit --source-root path may be supplied. Neither path is stored
in the receipt, which is deterministic across extraction locations.
No upstream Python or saved source schedule is executed, no original
source is changed, and no upload or public write is part of this audit.

See manuscript_review.md for the separate Report45 transcription review,
RECOVERY.json for byte-identity boundaries, receipt.json for fresh counts,
and MANIFEST.sha256 for this recovered packet's actual current hashes.

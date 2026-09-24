# A 44-operation ternary Pell kernel with no parity restriction

Replacing the two signed linear congruences by squared congruences gives
a kernel that supplies positive witnesses for either parity of its index.
The cost is 44 operations, one more than the fixed-parity kernel. This can
be useful when a surrounding encoding otherwise duplicates a masked field
solely to fix parity. No smaller complete universal system is claimed here.

## 1. Recovering an index from two squared congruences

Use the notation of `HALF_PARAMETER_PELL_92_PROOF.md`. Suppose the
independent main and relaxed norms have already given

    A>1, c=psi_A(p), f=chi_A(m), c|m, 0<2p<=m,
    R=ic^2, R^2=(A^2-1)(f^2-1),
    p>=7, 0<J<2p.

Supply positive integers u,j,o,y and impose

    R^2(u^2-y^2)=1-y^2,
    u^2=J^2+jc,
    u^2=c^2+of.                                    (1)

Then p=J. In particular, this conclusion needs no choice between positive
and negative residues of u.

The norm gives Ru=chi_R(s), y=psi_R(s), for a positive odd index
s=2h+1. The integer polynomial Q_h defined by chi_X(2h+1)=XQ_h(X^2)
satisfies

    u=Q_h(R^2),
    Q_h(1-A^2)=(-1)^h psi_A(s),
    Q_h(0)=(-1)^h s.

Modulo f, R^2=1-A^2. Thus u^2=c^2 modulo f implies
psi_A(s)^2=psi_A(p)^2 modulo f. The doubling identity gives
chi_A(2s)=chi_A(2p) modulo chi_A(m). The retained chi step-down
lemma, whose comparison-index hypothesis is 2p<=m, now gives
s=+/-p modulo m and hence modulo c.

Modulo c, R=0 and the same polynomial identity gives u^2=s^2=p^2.
The other squared congruence in (1) gives p^2=J^2 modulo c. Here the
size bound removes the possible composite-modulus ambiguity: since A>=2,

    c=psi_A(p)>=(2A-1)^(p-1)>=3^(p-1)>4p^2.

The last inequality holds at p=7 and propagates by induction. Both p^2
and J^2 therefore lie strictly between zero and c. Their congruence forces
equality as integers, so p=J. The argument does not infer a sign from a
square congruence modulo a composite number.

## 2. Positive auxiliary witnesses for both parities

For a canonical main index J=2r+1, choose the existing auxiliary values

    c=psi_A(J), m=2cJ, f=chi_A(m),
    R=(A^2-1)psi_A(m), i=R/c^2,
    y=psi_R(J), u=chi_R(J)/R.

The retained divisibility lemma makes i integral. The odd-index polynomial
makes u integral and yields

    u=(-1)^r c modulo f,
    u=(-1)^r J modulo c.

Consequently

    o=(u^2-c^2)/f, j=(u^2-J^2)/c                       (2)

are integers regardless of r's parity. The existing growth bound u>c>J
makes both strictly positive. Equations (1) follow. These choices replace
the old linear quotients, while every other canonical witness is retained.

## 3. The complete general-scale ternary kernel

Take positive input integers D0,r satisfying the explicit hypotheses

    D0>=81, r>=27, r<2D0, D0<r^2.                     (3)

The bounds are hypotheses of this component, not free comparisons in its
schedule. They are slightly broader than those of the original q^4 mask.
Use the 43-operation base-three kernel's mathematical parameters

    U=wD0, Y=sD0, E=UY, Q=UY^2, P=2Q+1,
    a=Y(U+1), A=a+3, M=6a+8, D=A^2-1,
    J=2r+1, R=ic^2, K=R^2.

Keep its first eight equations, and replace the final norm/congruence
block by (1). In full, the eleven source equations are

    tau(tau+1)=(E^2+U)(Yk)^2,
    c=Yk+eta, k=eta+zeta,
    k=r+1+hE,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+Dc^2,
    (ic^2)^2=D(f^2-1),
    D(f^2-1)(u^2-y^2)=1-y^2,
    u^2=J^2+jc,
    u^2=c^2+of.                                     (4)

All seventeen supplied auxiliaries are positive:
a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,gamma,y,u.
Here r is an input; a surrounding mask may instead count it as an
additional supplied unknown. Computed registers can be signed.

Under (3), positive solutions of (4) force

    U=3^(2r+1),
    D0 divides binom(2r,r).                           (5)

Conversely, if D0 is a power of three, (3) holds, and the divisibility
in (5) holds, then every positive auxiliary in (4) exists, for either
parity of r. The 44-operation count excludes construction of D0 and r,
the hypotheses (3), and any packing, computation or input interface.

Here are the required checks against the retained kernel proof, to make
the general scale and smaller thresholds explicit. From (3),

    U,Y>=D0, E>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<12/(D0+1)<=12/82<1/2.

The first norm and congruence give a first index t=r+1+vE with v>=0.
Since P>A and c>Yk>k, the main index satisfies p>=t+1>=r+2>=29.
Thus c>A^6>AD^2, 2p<=c, and J=2r+1<2p. The independent relaxed
rank lemma gives c|m and 2p<=m. Section 1 then recovers p=J.

The unchanged inequality (2P-1)-4A=4Y(U(Y-1)-1)-11>0 excludes v>=1,
so t=r+1. The exact-index Pell estimates with the displayed bound on
6r/a give, for xi=(U+1)^(2r)/U^r,

    Y>=U^r, a>U^(r+1), 0<c/k-xi<24r/(U+1).

The recurrence for chi_A(z)+(3-A)psi_A(z) gives U=3^J modulo M.
Because U<a<M and 3^J=3*9^r<U^(r+1)<a<M, it gives U=3^J exactly.
In particular D0, a divisor of U, is a power of three. The error is
then below 1/2, while the binomial tail is below 1/6. The interval
Y<c/k<Y+1 forces the exact integer part of xi, proving (5).

For the converse choose U=3^J, Y=floor(xi) and the same canonical first
and main Pell values as in `EXPLORATION_BASE_THREE_PELL_KERNEL.md`.
Since D0<r^2<U and both D0,U are powers of three, w=U/D0 is a
positive integer. The binomial expansion and assumed divisibility make
s=Y/D0 a positive integer. The retained ratio, index and exponent
arguments supply positive tau,h,eta,zeta,gamma. Section 2 supplies
the final positive auxiliaries without a parity condition.

## 4. Arithmetic and bounded evidence

The source checker is `../verification/explore_parity_free_pell_kernel.py`.
It replaces the old two constructions of u by the two constructions of
u^2 in (1). The product J^2 is the only extra primitive: u^2 and c^2
were already computed for the norms. Thus the schedule has

    44 operations = 26 multiplications + 18 additions/subtractions,
    eleven equality tests, seventeen positive auxiliaries.

All source polynomials are constructed afresh. The sole triangular
adjustment remains ((ic^2)^2-D(f^2-1))(u^2-y^2), so the schedule and
source systems have identical positive solutions.

The finite regression checks the enlarged preliminary inequalities,
the square-index size argument and canonical positive auxiliary tuples
of both parities. Those small auxiliary tuples check (1)-(2), not the
entire large-coordinate kernel. The complete theorem follows from the
general proof above and the explicitly retained Pell lemmas.

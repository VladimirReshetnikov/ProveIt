# A 74-operation native ternary increment history

The six-field 76-operation history can use five fields when its Pell kernel
is replaced by the independently proved parity-free version. Reusing the
already computed repunit double in the row geometry saves another addition.
The resulting complete relation has **74 operations: 37 multiplications and 37 additions
or subtractions**, 30 positive unknowns, and 21 equations. Its semantics are
unchanged: positive parameters encode the endpoints of a positive-length,
nonoverflow binary increment history in native ternary notation.

The predecessor proof and receipt remain frozen in
`EXPLORATION_NATIVE_TERNARY_HISTORY.md` and
`../verification/explore_native_ternary_history.py/.json`.
This version's full exact source, primitive schedule and finite receipt are
`../verification/explore_parity_free_ternary_history.py/.json`.
Its kernel dependency is `EXPLORATION_PARITY_FREE_PELL_KERNEL.md`.
This remains a bounded history component; no raw input conversion, program
control, halting construction, or improved universal bound is claimed.

## 1. Complete positive-integer system

The positive parameters are FI and FF. The twelve outer positive unknowns
are q,FA,FB,FD,FE,FC,Jrep,alpha,W,H,v,alphaI. The eighteen retained positive
unknowns are a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux,u. In particular
u is now supplied and positive; its square is already computed for a norm.
The duplicated occurrence of FC in the packed word is removed.

Put, as mathematical abbreviations,

    P0=FC+q FA+q^2 FB+q^3 FD+q^4 FE,
    D0=q^5,
    U=wD0, Y=sD0, E_pell=UY, Q_pell=UY^2,
    D_pell=(a+3)^2-1=a^2+6a+8, J_pell=2r+1.

The first ten equations are

    q=2Jrep+1,                                      (1)
    FE+Jrep=2FD+H,                                  (2)
    FC+Jrep=FD+FE,                                  (3)
    FA+FE=FB+FD,                                    (4)
    FA+FE+alpha=q+Jrep,                              (5)
    q=Wv,                                          (6)
    H(W-1)=q-1,                                    (7)
    FI+W FB=FA+q FF,                                (8)
    FI+alphaI=W,                                    (9)
    r=P0.                                         (10)

The remaining eleven equations are

    Q_pell(Q_pell+1)k^2=tau(tau+1),                (11)
    c=Yk+eta,                                      (12)
    k=eta+zeta,                                    (13)
    k=r+1+h E_pell,                                (14)
    a=Y(U+1),                                     (15)
    d=U+ac+gamma(6a+8),                            (16)
    d^2=1+D_pell c^2,                             (17)
    (ic^2)^2=D_pell(f^2-1),                        (18)
    D_pell(f^2-1)(u^2-y_aux^2)=1-y_aux^2,          (19)
    u^2=J_pell^2+jc,                               (20)
    u^2=c^2+of.                                    (21)

The fresh polynomial source uses precisely these abbreviations expanded
over the supplied variables. Two acyclic source corrections are used.
The schedule compares H(W-1) with the already computed 2Jrep, avoiding a
separate subtraction q-1. Its actual residual is the source residual of
(7) plus the source residual q-2Jrep-1 of (1). In (19), the residual of
(18) multiplied by u^2-y_aux^2 is the other correction. Both corrections
vanish by earlier equalities; neither changes the positive solution set.
All 21 comparisons are verified symbolically.

## 2. Paid preliminary bounds for the five-field word

Write J=Jrep and S=FA+FE=FB+FD. Positivity gives, before any decoding,

    q>=3, J=(q-1)/2, W>=2,
    S<=3J, 0<FA,FB,FD,FE<3J, 0<FC<5J.

For P4=FA+q FB+q^2 FD+q^3 FE, the opposite-pair equality gives

    P4=S(q^2+q^3)-(q^3-1)FA-(q^2-q)FB
       <=(3J-1)(q^3+q^2)+q+1.

It follows that

    q^4<P0=FC+q P4<3(q^5-1)/2.                    (22)

The algebraic upper-bound gap is explicitly positive: subtracting
5J+q[(3J-1)(q^3+q^2)+q+1] from 3(q^5-1)/2, and substituting
J=(q-1)/2, gives

    (q-1)(q+2)(2q^2+3q-1)/2>0.

With D0=q^5 and r=P0, the hypotheses of the general-scale parity-free
kernel are therefore established entirely by paid equations:

    D0>=243>=81, r>q^4>=81>27,
    r<3D0/2<2D0, D0<r^2.                          (23)

No parity condition is imposed or inferred. In fact the five-field index
can have either parity in genuine histories.

The theorem in `EXPLORATION_PARITY_FREE_PELL_KERNEL.md` applies to
(11)--(21) under exactly (23). It gives

    U=3^(2r+1), D0 divides binomial(2r,r).

Since q^5=D0 divides U, q is a power of three. Its independent main-index
argument is worth making explicit at the interface: preliminary growth
gives a main index p>=r+2>=29 and J_pell<2p. The two squared congruences
in (20),(21), together with the auxiliary Pell norm, give
p^2=J_pell^2 modulo c. The bound

    c=psi_(a+3)(p)>=3^(p-1)>4p^2

places both squares strictly between zero and c, forcing p=J_pell.
This does not infer a sign from a square congruence modulo a composite
number. The exact first index, exponent recurrence, ratio interval and
binomial rounding are then the retained general-scale proof. The kernel
has a positive converse for either parity, so no parity adapter is missing.

## 3. Mask decoding and the new single-FC carry argument

Write q=3^ell, L=q^5=3^N, N=5ell. The direct unit-two mask theorem states
that, in the window 0<=P<3(L-1)/2,

    L divides binomial(2P,P)

forces P<L, lowest ternary digit two, and every other one of its N
ternary digits one or two. For P<L this is the maximal-carry test.
For L<=P<L+(L-1)/2 the highest zero below the extra leading one stops
the doubling carry; at least two of the N+1 positions fail to carry.
The overflow valuation is therefore at most N-1. This is the same
sharp-window lemma proved in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`;
(22) supplies its required bound.

Every q-chunk of P0 consequently lies in [J,q-1]. Yet the supplied fields
must still be proved to equal those chunks. If FC>=2q, then FC<5J makes
its remainder modulo q less than J, which is impossible. If FC>=q,
the first native chunk implies

    FC>=q+J=3J+1,                                  (24)

and sends one carry to FA. Because FA<3J, any FA>=q would have remainder
FA+1-q<=J-1. The case FA=q-1 would instead give a zero chunk. Hence
FA<=q-2, and no carry reaches FB. The remaining fields FB,FD,FE have
no incoming carry. Each is less than 3J, so any one at least q would
have remainder at most J-2. They are therefore all native and below q.
In particular FD,FE<=q-1=2J, so (3) implies FC<=3J, contradicting
(24). This proves FC<q.

There is now no carry into FA. Applying the same elementary remainder
argument successively proves all five fields are below q and native.
The duplicated copy of FC was unnecessary for carry exclusion; its
previous purpose was to force an even packed index. The new kernel
removes that purpose without discarding any history.

## 4. Exact history semantics, including the endpoints

The remaining semantic proof uses only (1)--(9) and the five decoded
native fields, so it agrees with the predecessor. Here is the full
dependency order. From q=Wv and H(W-1)=q-1, one obtains

    W=3^m, q=W^t, m,t>=1,
    H=1+W+...+W^(t-1), J=jrow H, jrow=(W-1)/2.

The fact m divides log_3(q) follows by reducing 3^log_3(q)-1 modulo
3^m-1. Define Boolean words A=FA-J, B=FB-J, C=FC-J, D=FD-J, E=FE-J.
Equations (2)--(4) become

    E=2D+H, C=D+E, A+E=B+D,
    hence C=3D+H.                                  (25)

The sum 3D+H has raw digit sums at most two, so is carry-free in radix
three. Since C is Boolean, it has a one at each row head, and D has
a zero immediately before every row head. Its final digit is also
zero, because C<q. Thus every row starts with carry one and ends
with carry zero. At every cell, C=D+E and A+E=B+D have raw sides
at most two and say exactly that a zero source bit terminates an
incoming carry while a one source bit propagates it. Each row is
therefore one ordinary increment without overflow.

The input bound in (9) is retained and paid. Reducing (8) modulo W,
with 0<FI<W, shows FI is exactly the first native FA row. Comparing
the higher base-W rows shows every next FA row equals the preceding
FB row, and FF equals the last native FB row. No prior promise about
the digits of either parameter is used.

For code_m(n)=sum(bit_i(n)3^i,i<m), the exact endpoint relation is

    exists m,t>=1 and n>=0 such that n+t<2^m,
    FI=(3^m-1)/2+code_m(n),
    FF=(3^m-1)/2+code_m(n+t).                       (26)

Width and height are existential, but this particular endpoint predicate
is decidable. Neither numerical input conversion nor machine control
has been inferred from a counter history alone.

## 5. Positive converse for both packed-index parities

Given (26), take W=3^m, q=W^t, v=W^(t-1), and the displayed H,J.
At time j, let k_j<m be the number of trailing ones of n+j. Use raw rows

    A_j=code_m(n+j), B_j=code_m(n+j+1),
    D_j=(3^k_j-1)/2, E_j=3^k_j,
    C_j=(3^(k_j+1)-1)/2.

Concatenate them in base W and add J. All five fields are positive.
Since A and E have disjoint Boolean supports, S=FA+FE<=3J, so
alpha=q+J-S>=1. Also alphaI=W-FI>=1. This verifies every outer
equality with positive witnesses, including height one and alpha one.

The first C digit is one, so the first FC digit, and hence P0's unit
digit, is two. The five-field word is native and below q^5. Set r=P0,
D0=q^5. The direct mask gives central-binomial divisibility and (23)
gives every preliminary kernel bound.

All Pell witnesses must be chosen for this new r and D0; they are not
silently reused from the six-field certificate. The parity-free converse
chooses U=3^(2r+1), Y=floor((U+1)^(2r)/U^r), w=U/D0 and s=Y/D0,
then the canonical main and first Pell coordinates. The final positive
auxiliary construction takes

    J_pell=2r+1, c=psi_(a+3)(J_pell),
    m_aux=2cJ_pell, f=chi_(a+3)(m_aux),
    R=D_pell psi_(a+3)(m_aux), i=R/c^2,
    y_aux=psi_R(J_pell), u=chi_R(J_pell)/R,
    o=(u^2-c^2)/f, j=(u^2-J_pell^2)/c.

The last two quotients are integral for both parities because the old
linear congruences hold up to signs, and are positive because u>c>J_pell.
The full kernel proof establishes all other integrality and positivity
claims. Thus every history in (26) has all thirty positive witnesses.

## 6. Exact cost and reproducible checks

The nine outer equations and five-field Horner word use 27 operations.
Three products build q^2,q^4,q^5. The parity-free kernel uses 44 operations.
The total is therefore 74=37M+37A. Relative to 76, one Horner stage
costing one product and one addition is removed; the additional kernel
square costs one product; reusing 2Jrep=q-1 saves one subtraction. The
intermediate five-field construction before that last reuse costs 75.
All fixed numerals and equality comparisons
follow the existing free convention.

The exact checker serializes every instruction and verifies all 21 fresh
source residuals. Its finite regression recomputes 17,930 positive
pre-power tuples, 307,705 complete scalar candidates and 59 accepted
histories, plus 7,291 canonical histories through widths eight and heights
sixteen. The canonical set includes 43 alpha-one cases, 3,812 odd indices
and 3,479 even indices. Both parities are thus actually exercised.

The small tests do not instantiate the enormous full Pell tuples. Their
existence follows from the general positive converse, while the finite
regression checks the outer equations, carry recovery, exact endpoint
semantics and central-binomial valuation. No optimality or universal
operation bound follows from these finite results.

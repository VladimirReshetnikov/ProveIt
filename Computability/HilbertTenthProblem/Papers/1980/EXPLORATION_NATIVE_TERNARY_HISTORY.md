# A 76-operation bounded native ternary increment history

This note gives a complete positive-integer equation system for a finite
history of ordinary binary increments, with the bits represented as ternary
digits and with a native positive offset on every packed field. The initial
and final rows are positive parameters. Width and positive history length
are existential. The complete arithmetic certificate has **76 operations:
37 multiplications and 39 additions/subtractions**, with 29 positive unknowns
and 20 equations.

This is a bounded counter-history relation, not a universal computation
bound. Raw numerical input conversion, program control, and a halting
construction are not supplied. In particular it does not replace the
published universal certificate. The exact schedule, fresh source
polynomials, and finite regression are in
`../verification/explore_native_ternary_history.py` and its JSON receipt.
The earlier 63-operation single-ripple relation is preserved unchanged.

## 1. Why simply repeating the seed fails

Replacing the single seed by a geometric row-head mask in the four-field
ripple gives a 72-operation candidate. The following positive tuple refutes
its intended ordinary-increment semantics:

    W=9, q=81, v=9, H=10, Jrep=40,
    FA=44, FB=67, FD=53, FE=76,
    alpha=1, FI=8, FF=7, alphaI=1.

It satisfies

    q=Wv=2Jrep+1, H(W-1)=q-1,
    FE+Jrep=2FD+H,
    FA+FE=FB+FD,
    FA+FE+alpha=q+Jrep,
    FI+W FB=FA+q FF, FI+alphaI=W.

All four packed fields have four ternary digits in {1,2}. Their unshifted
values are A=4, B=27, D=13, E=36. The first row represents binary 3 -> 0;
the second represents 0 -> 2. An overflowing carry has combined with the
next seed. This is neither a nonoverflow history nor a correct two-step
history modulo four. The input and output rows themselves are correctly
native: FI=4+code_2(3), FF=4+code_2(2).

For the old four-field word P4, its old mask uses D0=3q^4 and r=3P4+2.
The word is native, r is even, q^3<P4<q^4, D0<r^2, and
v_3(binomial(2r,r))=17. Thus the enlarged even-r Pell-kernel converse
constructs every positive auxiliary witness. This is a full positive
counterexample to the naive 72-operation system, not merely a local carry
warning. The receipt evaluates every outer equality and the valuation;
it does not materialize the enormous Pell witnesses.

## 2. The complete new equations

The positive parameters are FI and FF. The twelve new positive unknowns are

    q, FA, FB, FD, FE, FC, Jrep, alpha, W, H, v, alphaI.

The seventeen retained positive unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

Uppercase H is the row-head mask; lowercase h is a Pell quotient. Put

    P0=FC+q FC+q^2 FA+q^3 FB+q^4 FD+q^5 FE,
    D0=q^6,
    U=wD0, Y=sD0, E_pell=UY, Q_pell=UY^2,
    D_pell=a^2+6a+8=(a+3)^2-1,
    J_pell=2r+1, u=J_pell+jc.

These displayed names are mathematical abbreviations, not extra supplied
unknowns or free arithmetic instructions. The first ten equations are

    q=2Jrep+1,                                         (1)
    FE+Jrep=2FD+H,                                     (2)
    FC+Jrep=FD+FE,                                     (3)
    FA+FE=FB+FD,                                       (4)
    FA+FE+alpha=q+Jrep,                                (5)
    q=Wv,                                             (6)
    H(W-1)=q-1,                                       (7)
    FI+W FB=FA+q FF,                                   (8)
    FI+alphaI=W,                                      (9)
    r=P0.                                            (10)

The remaining ten equations are the retained base-three kernel:

    Q_pell(Q_pell+1)k^2=tau(tau+1),                   (11)
    c=Yk+eta,                                         (12)
    k=eta+zeta,                                       (13)
    k=r+1+h E_pell,                                   (14)
    a=Y(U+1),                                        (15)
    d=U+ac+gamma(6a+8),                               (16)
    d^2=1+D_pell c^2,                                (17)
    (ic^2)^2=D_pell(f^2-1),                           (18)
    D_pell(f^2-1)(u^2-y_aux^2)=1-y_aux^2,             (19)
    u=c+of.                                          (20)

The code uses the shared-ratio-product form of (11), which is identically
equal to the displayed source. It evaluates (19) with (ic^2)^2 instead of
D_pell(f^2-1); the precise source difference is the residual of (18)
times (u^2-y_aux^2). Thus the correction is acyclic and vanishes by the
preceding equation. Every source polynomial is constructed independently
of the primitive schedule and compared symbolically.

## 3. All preliminary bounds precede the Pell argument

Write J=Jrep and S=FA+FE=FB+FD. Positivity in (1),(5),(9) gives

    q>=3, J=(q-1)/2, W>=2,
    S<=q+J-1=3J,
    0<FA,FB,FD,FE<=S-1<3J.

Equation (3) gives 0<FC=FD+FE-J<5J. No field has yet been asserted
to be native, and q has not yet been asserted to be a power of three.

Let P4=FA+q FB+q^2 FD+q^3 FE. The opposite-pair equality gives

    P4=S(q^2+q^3)-(q^3-1)FA-(q^2-q)FB
       <=(3J-1)(q^3+q^2)+q+1.

Consequently

    q^5<P0=q^2 P4+(q+1)FC<3(q^6-1)/2.               (21)

For clarity, substituting J=(q-1)/2 in the stated upper bound makes
the difference between 3(q^6-1)/2 and that upper bound exactly

    (q-1)(q+1)(2q^3+5q^2-2)/2>0.

The lower bound follows from the positive top field FE and all other
positive summands. For D0=q^6 and r=P0, (21) supplies

    D0>=729, r>q^5>=243,
    r<3D0/2<2D0, D0<r^2.                            (22)

In particular D0^2>r+1, D0(D0+1)>2r+1, and
6r/[D0(D0+1)]<12/(D0+1)<1/2. These are the range hypotheses
needed by the general-scale base-three kernel. Also r is already even:
q is odd, so

    r=P0=2FC+(FA+FB+FD+FE)=2FC+2S modulo 2.          (23)

No digit assumption was used for either (21) or (23).

The general-scale result is stated separately in
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`. Its even-sign branch is exactly
(11)--(20). To make the interface explicit: from D0>=243, r>=83,
r<2D0, and D0<r^2 it recovers U=3^(2r+1) and
D0 | binomial(2r,r). Its proof only uses a lower bound on D0 and the
displayed inequalities; it does not assume D0 is square or of the form
3q^4. Briefly, U,Y>=D0 imply E_pell>r+1 and a>2r+1. The first
Pell index is r+1 modulo E_pell; the main index is at least r+2>=85.
The relaxed auxiliary rank and signed index argument therefore apply
before any exponent decoding. They recover the main index 2r+1 and
then the first index r+1. The ratio bounds give

    xi<c/k<xi(1+12r/a), xi=(U+1)^(2r)/U^r,
    Y>=U^r, a>U^(r+1).

The recurrence for chi_(a+3)(j)-a psi_(a+3)(j) gives 3^j modulo
6a+8. Both U and 3^(2r+1) lie strictly between zero and this modulus,
so the exponential congruence is an equality. The small binomial tail
then gives Y=floor(xi) and the central-binomial divisibility. Since
D0=q^6 divides 3^(2r+1), q is a power of three. The cited proof supplies
the full estimates and every positive witness in the converse.

## 4. The unit-two mask and the overflow window

Write q=3^ell and L=q^6=3^N, where N=6ell. If 0<=P<L, doubling
P has at most N carries. All N occur precisely when its lowest ternary
digit is two and all higher N-1 digits are one or two. This follows
one digit at a time: the first carry requires 2+2>=3, and, once a
carry is present, a higher digit emits a carry precisely when it is
positive. By Kummer's theorem,

    L | binomial(2P,P)

is equivalent to that digit condition for P<L.

It is essential to exclude overflow before extracting fields. If
P=L+x with 0<=x<(L-1)/2, compare x with the N-digit all-one word.
At their highest differing position x has a zero; all positions above
it have digit one. The zero stops any incoming doubling carry, and
the higher ones, including the extra top one of P, cannot restart it.
At least two among the N+1 positions have no outgoing carry. Hence
v_3(binomial(2P,P))<=N-1, so the mask rejects this entire interval.

The strict preliminary bound (21) lies inside this rejection interval
when P0>=L. Thus the kernel implies

    P0<L, P0 mod3=2,
    all N ternary digits of P0 belong to {1,2}.       (24)

The direct choice r=P0 and D0=q^6 saves three operations compared
with using D0=3q^6 and r=3P0+2. The guard will force the lowest field
to have unit digit two in every genuine history; this is proved below,
rather than assumed as an external input condition.

## 5. Recovering all six fields despite possible carries

Every q-digit chunk of the native word in (24) is at least J and at
most q-1=2J. First consider the duplicated low field FC.

Because FC<5J, if FC>=2q its remainder modulo q is less than J.
This contradicts the lowest native chunk. Hence FC<2q. Suppose
FC>=q. Its lowest chunk is FC-q>=J, so

    FC>=q+J=3J+1.                                   (25)

The carry into the second copy of FC is one. FC=2q-1 would make
that second chunk zero, which is impossible. Otherwise FC+1 still
has carry one and passes that carry to FA. Since FA<3J, FA>=q
would make the next remainder FA+1-q<=J-1, also impossible.
The case FA=q-1 would again make that chunk zero. Therefore
FA<=q-2, and no carry reaches FB.

Now FB, FD, FE have no incoming carry. Each is less than 3J, so any
one of them at least q would have remainder at most J-2. Inducting
through these three chunks proves they are all less than q and native.
In particular FD,FE<=q-1=2J. But (3) then gives FC<=3J, contradicting
(25). Thus FC<q after all.

There is consequently no carry out of either copy of FC. Applying
the same elementary chunk argument to FA,FB,FD,FE proves

    0<FC,FA,FB,FD,FE<q,
    every one of their ell ternary digits is one or two. (26)

The order and duplication of FC are purposeful. Assuming its native
range before this argument would hide the main possible carry alias.

## 6. Geometry, row guards, and exact increment semantics

From q=3^ell, q=Wv, and W>=2, write W=3^m with m>=1. Equation
(7) implies 3^m-1 divides 3^ell-1. Division with remainder on ell
shows m divides ell. Thus

    t=ell/m>=1, q=W^t,
    H=1+W+...+W^(t-1),
    J=jrow H, jrow=(W-1)/2.

Define the nonnegative Boolean ternary words

    A=FA-J, B=FB-J, C=FC-J, D=FD-J, E=FE-J.

Equations (2)--(4) become

    E=2D+H, C=D+E, A+E=B+D,
    and therefore C=3D+H.                           (27)

The last equality is carry-free: 3D and H have only zero-one digits,
so every raw sum is at most two. Since C is Boolean, their supports
are disjoint. At every row head H has digit one, so the preceding
row's last D digit is zero, while the first C digit is one. The final
D digit is also zero because C<q. Thus no row can pass an outgoing
carry to its successor. In particular C's unit digit is one and FC's
unit digit is two, as required by the direct mask.

Both sides of C=D+E and A+E=B+D have raw digit sums at most two.
They therefore hold digitwise. At one cell their Boolean solutions are

    C=0: D=E=0 and B=A;
    C=1,A=0: D=0,E=1,B=1;
    C=1,A=1: D=1,E=0,B=0.

These are exactly the ordinary increment cell: C is the incoming carry,
D the outgoing carry, E the position where it terminates, and B the
updated bit. The spatial equality in (27) supplies incoming carry one
at each row head and otherwise propagates the preceding D digit.
Since each row ends with D=0, every row increments without overflow.

It remains to check the initial and final interfaces without assuming
their parameters are native. Native fields have base-W rows in
[jrow,W-1]. Reduce (8) modulo W. Since 0<FI<W by (9), and the
lowest row of FA lies in that same range, FI equals that row exactly.
Comparing the higher base-W rows of (8) gives each next FA row equal
to the previous FB row, and FF equal to the last FB row. All these
comparisons have no carries, since the fields are below q and every
row is below W. This proves, rather than assumes, the native coding
of both endpoints.

For a nonnegative integer n<2^m define

    code_m(n)=sum(bit_i(n)*3^i, i=0,...,m-1).

The exact relation defined by all twenty equations is therefore:

    there are m>=1, t>=1, and n>=0 with n+t<2^m,
    FI=(3^m-1)/2+code_m(n),
    FF=(3^m-1)/2+code_m(n+t).                        (28)

This finite endpoint relation is decidable. The native size range of FI
determines its possible width; the decoded endpoint difference determines
t. The purpose here is a counted history interface, not an assertion of
Turing completeness.

## 7. Every history in (28) has positive witnesses

Given m,t,n as in (28), choose W=3^m, q=W^t, v=W^(t-1), H and J
as above. At time j, let k_j be the number of trailing one bits of n+j.
Nonoverflow means 0<=k_j<m. Use the raw rows

    A_j=code_m(n+j), B_j=code_m(n+j+1),
    D_j=(3^k_j-1)/2, E_j=3^k_j,
    C_j=(3^(k_j+1)-1)/2.

Concatenate the rows in base W and add J to obtain the five native
fields. Equations (2)--(4) and (8) now hold exactly. All fields are
strictly positive, including FD even when every raw D row is zero.

At every cell E=1 means the source bit A is zero. Thus A+E is Boolean
and at most J. Consequently

    S=FA+FE=2J+A+E<=3J,
    alpha=q+J-S>=1.

Also alphaI=W-FI>=1. The row geometry witnesses are all positive,
including v=1 when t=1. The six-field word P0 is native; its lowest
digit is two because C's first digit is one. It is even by (23).
Set r=P0 and D0=q^6. The direct mask supplies the central-binomial
divisibility, and (22) supplies every preliminary bound of the
general-scale even-r kernel converse. That converse constructs all
seventeen positive Pell witnesses. In particular it takes
U=3^(2r+1), Y=floor((U+1)^(2r)/U^r), w=U/D0 and s=Y/D0;
their integrality uses D0<r^2<U and central-binomial divisibility.
The remaining positive quotients and auxiliary Pell coordinates are
the unchanged explicit formulas in the cited kernel proof.

No numeric computation of those enormous witnesses is used as a
substitute for this existence proof.

## 8. Arithmetic and finite evidence

The schedule charges 30 operations for all outer equations and the
six-field Horner word, three products for q^2,q^4,q^6, and the retained
43 operations. Thus it totals 76=37M+39A. Equality tests and fixed
numerals are free. Duplication of FC is achieved by using the same
supplied field twice; no second supplied copy or equality is hidden.

The two added guard additions, two additional Horner stages, and one
additional power product would turn the naive 72 into a guarded 79
using the earlier mask. The direct unit-two mask removes two products
and one addition, giving the stated 76. The actual receipt contains
every primitive instruction rather than relying only on this delta.

The deterministic regression separately verifies:

- 17,930 positive preliminary tuples for odd q from 3 through 63;
- 307,705 complete scalar candidates of total ternary widths 1 through 5,
  with 59 accepted histories, each checked against exact binary increments;
- 7,291 canonical histories of bit widths 1 through 8 and positive heights
  at most 16, including 43 cases with alpha=1;
- the full positive outer counterexample to the naive 72 system.

These finite checks supplement the general proofs of range recovery,
carry exclusion, exact history semantics, and positive Pell existence.
They establish neither an exhaustive search over all system designs nor
an improved universal certificate bound.

# An 82-operation activated native counter history

This note adds a variable row-head activation signal to the complete
74-operation native increment history. Every row increments or holds
according to its own decoded Boolean activation bit. The complete system
has **82 operations: 40 multiplications and 42 additions/subtractions**,
32 positive unknowns, and 22 equations. All fixed numerals and equality
tests have the existing free convention.

The proof supplies a bounded arithmetic component, not a universal machine.
Program routing, raw numerical input conversion, a zero branch, and halting
remain separate. In particular its operation count does not improve the
published universal frontier. The control field is an output of this
relation that a future program relation may share; it is not presumed
typed for free. The full source, schedule, and finite receipt are in
`../verification/explore_controlled_native_counter.py/.json`.

## 1. Why an inactive next row needs an independent guard

For Boolean ternary words, the local increment equations are

    C=D+E, A+E=B+D.

An active incoming carry C either propagates through a one bit as D or
terminates at a zero bit as E. An inactive bit stays unchanged. A row-head
mask H normally wires C=3D+H. Its Booleanity also makes D zero just before
every row head. Replacing H by a subset K would lose that boundary check
before inactive rows.

Here is an exact counterexample to the tempting variant that merely uses
C=3D+K. Take

    W=9, q=81, J=40, H=10,
    raw A=4, B=9, D=4, E=9, C=13, K=1, Kbar=9.

All these raw words are Boolean ternary words below q, K+Kbar=H, and

    C=D+E=3D+K, A+E=B+D.

The two rows are binary 3->0 and 0->1, although their activation bits
are 1 and 0. A carry has crossed the boundary. Their native values and
positive endpoint witnesses are

    FA=44, FB=49, FD=44, FE=49, FC=53,
    FK=41, FKbar=49, FI=8, FF=5, alpha=28, alphaI=1, v=9.

Every ordinary time, head-support, and shared-bound equation below holds.
Packing FC first followed by the other six fields gives a native word
with unit digit two; the direct ternary mask and general-scale parity-free
Pell converse supply every positive Pell witness. Thus simply substituting
K in the old guard produces a full false history, even with a typed K.

The replacement here separates the boundary guard from the active carry:

    E=2D+K, G=3D+H.                               (1)

G is Boolean and keeps every row boundary closed. Once K is proved a
Boolean subset of H, C=D+E=G-H+K is Boolean: replace each head one of G
by the corresponding K bit. This has the intended active/held-row wiring.
No supplied C field is needed.

## 2. Complete equations and exact cost

The positive parameters are FI and FF. The fourteen outer positive
unknowns are

    q,FA,FB,FD,FE,FG,FK,FKbar,J,alpha,W,H,v,alphaI.

The eighteen retained positive unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux,u.

The checker names J as Jrep and gamma as ga. The first eleven equations are

    q=2J+1,                                       (2)
    FE+2J=2FD+FK,                                 (3)
    FG+2J=3FD+H,                                  (4)
    FA+FE=FB+FD,                                  (5)
    FA+FE+alpha=q+J,                              (6)
    q=Wv,                                         (7)
    H(W-1)=q-1,                                  (8)
    FI+W FB=FA+q FF,                              (9)
    FI+alphaI=W,                                 (10)
    FK+FKbar=2J+H,                               (11)
    r=FG+q FA+q^2 FB+q^3 FD+q^4 FE+q^5 FK+q^6 FKbar. (12)

Write P for the right side of (12), and D0=q^7. The remaining eleven
equations are exactly the general-scale parity-free ternary kernel in
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`. Explicitly, put

    U=wD0, Y=sD0, Q_pell=UY^2,
    Delta=(a+3)^2-1=a^2+6a+8, J_pell=2r+1.

Its equations are

    Q_pell(Q_pell+1)k^2=tau(tau+1),
    c=Yk+eta, k=eta+zeta, k=r+1+hUY,
    a=Y(U+1), d=U+ac+gamma(6a+8),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u^2=J_pell^2+jc, u^2=c^2+of.                 (13)

The geometry double 2J is shared with (8), so the schedule compares
H(W-1) directly with 2J. The exact residual is source(8)+source(2).
The final norm uses (ic^2)^2 in place of Delta*(f^2-1), with the retained
acyclic correction from the preceding relaxed norm. All other source
comparisons are exact polynomial identities. The checker verifies all
twenty-two expanded source residuals independently of the primitive list.

Equations (2)--(11) take 22 operations. The seven-field Horner word takes
12. The chain q^2,q^3,q^4,q^7 takes four products. The kernel takes 44.
Thus the complete total is 22+12+4+44=82. Relative to 74, the independent
guard costs one extra addition, typing K and its complement costs two,
two extra Horner stages cost four, and the q^7 chain costs one extra
product. A duplicated low guard would instead give 83; Section 4 shows
why it can be omitted.

## 3. Preliminary bounds do not assume any digits

Put S=FA+FE=FB+FD. Positivity, (2), and (6) give

    q>=3, J=(q-1)/2, S<=3J,
    0<FA,FB,FD,FE<3J.

By (10), W>=2. Because q is odd and W divides q, W is odd and W>=3.
Equation (8) therefore gives 0<H<=J. Equation (11) gives

    FK+FKbar=2J+H<=3J, 0<FK,FKbar<3J.

Using (3),

    2FD=FE+2J-FK<=5J-2,
    0<FG=3FD+H-2J<13J/2.                        (14)

No Booleanity or power-of-three assertion has entered these bounds.
For P4=FA+q FB+q^2 FD+q^3 FE, the opposite-pair constraint gives

    P4<=(3J-1)(q^3+q^2)+q+1.

The head pair gives q^5 FK+q^6 FKbar<=q^5+(3J-1)q^6. Consequently

    q^6<P
       <13J/2+q[(3J-1)(q^3+q^2)+q+1]+q^5+(3J-1)q^6
       <3(q^7-1)/2.                             (15)

The final inequality holds for every real q>=3 after substituting
J=(q-1)/2. The exact checker expands its difference at q=t+3 and verifies
that every coefficient is positive. This is a polynomial verification of
the displayed bound, not a finite numerical substitute.

Thus r=P,D0=q^7 satisfy D0>=81,r>=27,r<2D0,D0<r^2. These are all the
independent hypotheses of the general-scale kernel. It recovers

    U=3^(2r+1), D0 divides binomial(2r,r),

with no parity assumption. Hence q is a power of three. The same geometry
argument as in the retained history gives W=3^m, q=W^t for m,t>=1,

    H=1+W+...+W^(t-1), J=jrow H, jrow=(W-1)/2.    (16)

In particular H is now Boolean, proved before the field-carry argument.

## 4. One low guard suffices for field recovery

The direct unit-two mask in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`,
together with (15), gives P<q^7, unit digit two, and every other ternary
digit one or two. Every q-chunk is therefore native and in [J,q-1].
It remains to show that the supplied fields are those chunks.

Only FG has the weaker bound in (14). If FG>=3q, its remainder is less
than J: indeed FG<13J/2 and 3q=6J+3; also FG<4q. This contradicts the
lowest native chunk. The carry from FG is therefore 0, 1, or 2.

Suppose it is 2. If FA+2 sends a carry onward, its remainder must be at
least J. Since FA<=3J-1, the only possibility is FA=3J-1, with remainder J.
Then S<=3J forces FE=1. The seed gives 2FD=1+2J-FK<=2J, so FD<=J and
FG<=J+H<=2J<q, contradicting the initial carry 2. Otherwise FA absorbs
the carry. The remaining fields, each less than 3J, have no incoming carry;
any one at least q would have remainder at most J-2. Induction makes
FB,FD,FE,FK,FKbar all native and below q. In particular FD<=2J and
FG=3FD+H-2J<=4J+H<=5J. But two q carries with a native low chunk require
FG>=2q+J=5J+2, another contradiction.

Suppose instead the carry is 1. If FA>=q, the next remainder is at most
J-1; FA=q-1 would give zero. Thus FA<=q-2 and the carry is absorbed.
The same elementary chunk induction makes FB,FD,FE,FK,FKbar native and
below q. Define their raw Boolean words D=FD-J,E=FE-J,K=FK-J and
Kbar=FKbar-J. Their equations now give

    E=2D+K, K+Kbar=H.

In particular K>=0 and E<=J, so D<=J/2<q/3. D has zero highest ternary
digit. The polynomial digit sums in 3D+H are at most two; no carry occurs,
and the highest possible place is below q. Hence 3D+H<q. Equation (4)
now gives FG=J+3D+H<q+J. A carry 1 with a native low chunk requires
FG>=q+J, contradiction.

There is therefore no carry from FG. Every other field is below 3J and
has no incoming carry, so the elementary induction proves that all seven
fields equal their native q-chunks. No field bound was assumed from its
intended semantics, and no duplicated guard is required.

## 5. Controlled rows and exact endpoint semantics

Subtract J from every native field, writing its raw word by the same
letter without F. Equation (11) becomes K+Kbar=H. Raw sums are at most
two, so this is digitwise. Thus K is a Boolean subset of the row heads
and Kbar is its exact complement in H.

Equations (3)--(5) become

    E=2D+K, G=3D+H, A+E=B+D.                    (17)

Because G is Boolean, the carry-free sum 3D+H has disjoint supports.
Thus D is zero immediately before every row head and at the final place.
Define C=D+E=3D+K=G-H+K. This is Boolean, with incoming carry K at each
head and the previous D digit at each nonhead. The exact local equations
C=D+E and A+E=B+D now hold digitwise: an active carry propagates through
a one, terminates at a zero, and changes that bit; inactive cells hold.
Every row ends with carry zero independently of whether the next row is
active. A row with head bit zero holds, and a row with head bit one performs
one ordinary nonoverflow increment.

The paid endpoint bound 0<FI<W and equation (9) give FI as the first
native FA row, consecutive FA rows as the previous FB rows, and FF as the
final native FB row. No digit promise about FI or FF is supplied.

For code_m(n)=sum(bit_i(n)3^i,i<m), the full relation has this exact
interpretation: there exist m,t>=1, activation bits epsilon_0,...,epsilon_(t-1),
and n>=0 with n+sum epsilon_j<2^m such that

    FI=(3^m-1)/2+code_m(n),
    FF=(3^m-1)/2+code_m(n+sum epsilon_j),
    FK=J+sum epsilon_j W^j, FKbar=J+sum(1-epsilon_j)W^j,

and the intermediate counter follows those increments and holds in order.
Without another relation constraining FK, this endpoint predicate is
decidable. Supplying FK as a shared input to another relation changes
neither its typing proof nor the charged schedule; it does not make that
other relation free.

## 6. Positive converse

For any such history choose W=3^m,q=W^t,v=W^(t-1), and H,J as in (16).
At row j, let n_j be its input. If epsilon_j=0, take D_j=E_j=0 and G_j=1.
If epsilon_j=1, let k_j<m be the number of trailing one bits of n_j and take

    D_j=(3^k_j-1)/2, E_j=3^k_j, G_j=3D_j+1.

Take A_j=code_m(n_j), B_j=code_m(n_j+epsilon_j), and concatenate each
field in base W, then add J. K and its complement are the displayed head
bits, also made positive by adding J. All seven fields are strictly
positive even when the entire raw control or carry word is zero.

At every cell, A and E are disjoint: an E bit terminates a carry at a zero
source bit. Thus FA+FE<=3J and alpha=q+J-FA-FE>=1. Also alphaI=W-FI>=1.
Every outer equality holds with positive witnesses, including all-hold
histories and height one. G's first raw digit is one even when the initial
activation is zero, so FG has unit digit two. The packed word is native
and below q^7. Its direct mask gives D0-divisibility, and (15) supplies
the general-scale bounds. The parity-free positive converse supplies all
seventeen remaining positive auxiliaries for the already fixed r=P,D0=q^7. It applies to either
packed-index parity; no numerical evaluation of enormous witnesses is
being substituted for their existence proof.

## 7. Exact evidence and remaining program obligations

The source checker verifies all 82 primitive instructions and 22 expanded
residuals. Its finite phase checks 45,570 positive preliminary tuples,
7,517 complete power-three outer candidates with 34 accepted histories,
and 3,230 canonical histories. These include 310 all-hold histories and
76 cases with alpha=1. It also records the false old-guard tuple from
Section 1, its complete field mask and exact central-binomial valuation,
and its full positive Pell-extension hypotheses.

This is a bounded conditional-increment building block. Its activation
typing can be shared with a separately verified finite-program lookup,
but the lookup, conditional decrement/zero routing, common variable frame,
and raw input contract still require a counted and proved composition.

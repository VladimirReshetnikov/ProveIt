# Fixed-many interleaved native counters in 85 operations

Fix any integer k>=2. The number k is a property of the component, not a
supplied unknown. Put p=3^k and jblock=(p-1)/2; these are free fixed
numerals. A single ternary word can store k ordinary binary counters in
the positions congruent to 0,...,k-1. Replacing the carry step three by p
in the activated counter component gives a complete simultaneous
increment/hold history with the same seven masked fields.

The complete certificate has **85 operations, 44 multiplications and
41 additions/subtractions**, with 33 positive unknowns and 23 equations.
The count is independent of fixed k. The source and exact symbolic
coefficient-template check are in
`../verification/explore_interleaved_native_counters.py/.json`.

This is a finite-history component. It does not supply decrement, zero
testing, program control, halting, or a conversion from an ordinary raw
numerical input into its interleaved native code. In particular it is not
an improvement to the universal frontier. Its control output specifies
an arbitrary subset of the k counters to increment at each row.

## 1. The row geometry must not be absorbed into the head mask

One tempting formulation uses only the mask H_all of the first k cells
of each row and asserts

    H_all(W-1)=(p-1)J, q=2J+1, q=Wv,
    W-1=(p-1)width_multiple.

These equations do not force q=W^t after q is known to be a power of
three. Cancellation by the fixed factor jblock can conceal a partial
last row. The smallest illustrative complete outer witness is

    p=W=9, q=27, J=H_all=13, v=3, width_multiple=1,
    FA=FB=FD=FE=FK=13, FG=FKbar=26,
    FI=FF=4, alpha=14, alphaI=5.

It satisfies the proposed seed, guard, activation, pair, bound, and time
equations. Every packed field is native, the low guard has unit digit two,
and the central-binomial valuation is 21, exactly the q^7 threshold.
The general-scale parity-free Pell converse supplies all positive
auxiliaries. Nevertheless log_3(q)=3 is not a multiple of log_3(W)=2.
This refutes the proposed exact row geometry, rather than the validity of
the particular all-hold endpoints.

The safe system retains the ordinary row repunit H and computes

    H_all=jblock H.

It keeps H(W-1)=q-1 and separately imposes W-1=(p-1)width_multiple.
This costs one additional product over the failed absorbed geometry.

## 2. Source equations and exact schedule

The positive parameters are FI and FF. The outer positive unknowns are

    q,FA,FB,FD,FE,FG,FK,FKbar,J,alpha,W,H,v,alphaI,width_multiple.

The eighteen retained positive unknowns are

    a,c,d,f,h,i,j,k_pell,o,r,s,w,tau,eta,zeta,gamma,y_aux,u.

The checker uses `Jrep`, `ga`, and `k` for J, gamma, and k_pell.
H_all is a computed quantity, not another supplied unknown. The twelve
outer equations are

    q=2J+1,
    FE+(p-1)J=(p-1)FD+FK,
    FG+(p-1)J=pFD+jblock H,
    FA+FE=FB+FD,
    FA+FE+alpha=q+J,
    q=Wv,
    H(W-1)=q-1,
    FI+W FB=FA+q FF,
    FI+alphaI=W,
    FK+FKbar=2J+jblock H,
    r=FG+q FA+q^2 FB+q^3 FD+q^4 FE+q^5 FK+q^6 FKbar,
    W-1=(p-1)width_multiple.                              (1)

Write P for the displayed seven-field word and D0=q^7. The remaining
eleven equations are the full general-scale parity-free ternary Pell
kernel in `EXPLORATION_PARITY_FREE_PELL_KERNEL.md`, with this D0 and r.
Equivalently, put

    U=wD0, Y=sD0, Q_pell=UY^2,
    Delta=(a+3)^2-1, J_pell=2r+1.

Those equations are

    Q_pell(Q_pell+1)k_pell^2=tau(tau+1),
    c=Y k_pell+eta, k_pell=eta+zeta,
    k_pell=r+1+hUY,
    a=Y(U+1), d=U+ac+gamma(6a+8),
    d^2=1+Delta c^2,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u^2=J_pell^2+jc, u^2=c^2+of.                        (2)

The outer schedule is obtained from the frozen controlled82 schedule by
the following explicit changes:

* Construct (p-1)J once and share it between seed and guard.
* Construct jblock H once and share it between guard and activation typing.
* Replace FD+FD by (p-1)FD, then add FD to obtain pFD.
* Construct (p-1)width_multiple and compare it with the already computed
  W-1. This final comparison needs no additional subtraction.

There are three additional products and one existing addition changes
to a product. Thus 40M+42A becomes 44M+41A, a total of 85. The seven-field
Horner packing still costs twelve operations, q^2,q^3,q^4,q^7 still cost
four, and the kernel still costs 44. The remaining outer work costs 25.

All 23 expanded source residuals are checked. As in controlled82, the
geometry comparison H(W-1)=2J adds the first source residual to the
written q-1 source residual. The half-parameter norm uses its existing
acyclic correction from the preceding relaxed norm. The checker also
verifies the entire source template with p symbolic, so its equality
claims do not depend on sampling a few particular fixed strides.

For k=1 the frozen82 specialization is cheaper: its doubling uses an
addition, H_all=H, and the extra width congruence is unnecessary. The85
count here concerns arbitrary fixed k>=2.

## 3. Bounds before any digit interpretation

Set S=FA+FE=FB+FD. Positivity and the first and fifth equations give

    q=2J+1>=3, S<=3J,
    0<FA,FB,FD,FE<3J.                                (3)

The positive width_multiple gives W>=p>=9. The two geometry equations
give

    H=(q-1)/(W-1),
    0<H_all=jblock H=(p-1)J/(W-1)<=J.                 (4)

No power assertion is needed for (4). Activation typing therefore gives

    0<FK,FKbar<3J.

The seed and positivity give

    (p-1)FD=FE+(p-1)J-FK <= (p+2)J-2.

Consequently

    FG=pFD+H_all-(p-1)J
      <= (5+3/(p-1))J-2p/(p-1)
       <13J/2.                                      (5)

The last inequality is valid for every p>=3. Hence the complete
preliminary bounds from controlled82 apply without change. Explicitly,
opposite pairs in S give

    P4=FA+q FB+q^2 FD+q^3 FE
       <=(3J-1)(q^3+q^2)+q+1,

and the flag pair gives

    q^5 FK+q^6 FKbar <= q^5+(3J-1)q^6.

Together with (5),

    q^6<P
       <13J/2+q[(3J-1)(q^3+q^2)+q+1]+q^5+(3J-1)q^6
       <3(q^7-1)/2.                                 (6)

The final polynomial bound is precisely the symbolic positive-gap
identity checked in controlled82; it is independent of p. Thus
D0>=81, r>=27, r<2D0, and D0<r^2 hold before decoding. The complete
general-scale kernel applies and recovers U=3^(2r+1) and
D0 dividing binomial(2r,r). In particular q is a power of three.

Because W divides q, write W=3^m and q=3^ell. The retained equation
H(W-1)=q-1 now gives m|ell, so ell=mt for an integer t>=1. The added
width equation says 3^k-1 divides 3^m-1, and hence k|m. Write m=kn,
where n>=1. We have proved

    W=3^(kn), q=W^t,
    H=1+W+...+W^(t-1),
    H_all=(1+3+...+3^(k-1))H.                        (7)

In particular H_all is a Boolean ternary word with ones at exactly the
first k positions of every complete row. This conclusion precedes the
packed-field recovery argument.

## 4. Recovery of all seven supplied fields

The enlarged-domain direct unit-two mask, together with (6), gives
P<q^7, unit digit two, and every other ternary digit one or two. Every
normalized q-chunk is therefore native and lies in [J,q-1]. We must
prove that those chunks equal the supplied fields.

All fields except FG are less than 3J, while FG<13J/2. If FG>=3q its
remainder is less than J, since 3q=6J+3 and FG<4q. This is impossible.
The initial carry is therefore zero, one, or two.

Suppose it is two. If FA+2 carries onward with a native remainder,
FA<=3J-1 forces FA=3J-1. Then S<=3J forces FE=1. The seed gives

    (p-1)FD=1+(p-1)J-FK <=(p-1)J,

so FD<=J and FG<=J+H_all<=2J<q, a contradiction. Otherwise FA absorbs
the carry. Every following field is less than 3J and has no incoming
carry. A field at least q would have remainder at most J-2, so induction
makes FB,FD,FE,FK,FKbar native and below q.

If the initial carry is one, FA cannot carry onward: FA+1 would have
remainder at most J-1, and FA=q-1 would give zero. Thus FA absorbs it,
and the same induction makes all the later fields native.

In either remaining case define raw Boolean words
D=FD-J, E=FE-J, K=FK-J, and Kbar=FKbar-J. They satisfy

    E=(p-1)D+K, K+Kbar=H_all.

In particular K>=0 and E<=J, so

    D<=J/(p-1)<q/p.                                 (8)

The top k ternary digits of D vanish. The raw polynomial digit sums in
pD+H_all are at most two, so they create no carries; by (8) both summands
have support strictly below q. Consequently pD+H_all<q. The guard now
gives

    FG=J+pD+H_all<q+J.

But either a carry one or a carry two with a native low chunk requires
FG>=q+J. This excludes both cases. There is no initial carry, and the
usual chunk induction proves that all seven fields equal their native
chunks. The argument never assumes nonnegative raw controls before
their own fields have decoded.

## 5. Exact interleaved history semantics

Subtract J from each supplied native field. The raw equations become

    E=(p-1)D+K,
    G=pD+H_all,
    A+E=B+D,
    K+Kbar=H_all.                                  (9)

The last equation is carry-free and makes K an arbitrary Boolean subset
of the first k positions in each row. Because G is Boolean, pD and
H_all have disjoint supports. Thus D vanishes in the last k positions
of every row, including the final row.

Define C=D+E=pD+K=G-H_all+K. Replacing the head ones of G by the selected
K bits shows that C is Boolean. Both C=D+E and A+E=B+D now hold digitwise:
each side is the sum of two Boolean words, so no ternary carry occurs.
Their scalar rule is the exact active increment cell. A carry propagates
through a one bit as D, terminates at a zero bit as E, and toggles that
bit. An inactive bit is unchanged.

The shift p=3^k connects only positions in the same residue class modulo
k. Thus each row contains k independent n-bit counters. The K bit at
position a selects counter a, for 0<=a<k. The boundary guard prevents
overflow for every lane, regardless of the activation pattern in the
next row. Several counters may increment simultaneously, and every
counter may hold.

For a vector z=(z_0,...,z_(k-1)), define

    interleave_(k,n)(z)
      =sum_(a=0)^(k-1) sum_(i=0)^(n-1) bit_i(z_a) 3^(ki+a).

The complete positive endpoint relation is exactly this: there exist
n,t>=1, a vector z of nonnegative integers, and activation vectors
epsilon_0,...,epsilon_(t-1) in {0,1}^k such that

    z_(j+1)=z_j+epsilon_j,
    every coordinate of every z_j is less than 2^n,
    FI=(3^(kn)-1)/2+interleave_(k,n)(z_0),
    FF=(3^(kn)-1)/2+interleave_(k,n)(z_t).

Moreover FK and FKbar expose the native concatenations of the activation
blocks and their complements. The paid input bound FI<W and the time
equation recover FI as the first FA row, each later FA row as the
preceding FB row, and FF as the final FB row. There is no assumed digit
promise about either endpoint parameter.

## 6. Complete positive converse

Given such a history, use W=3^(kn), q=W^t, v=W^(t-1), J=(q-1)/2,
H=(q-1)/(W-1), and width_multiple=(W-1)/(p-1). All these witnesses are
positive integers.

For each active lane a at a row, let ell_a<n be the number of trailing
one bits of its source counter. Use the raw carry and termination words

    D_row=sum_(active a) 3^a (p^ell_a-1)/(p-1),
    E_row=sum_(active a) 3^a p^ell_a,
    K_row=sum_(active a) 3^a,
    G_row=p D_row+jblock,
    Kbar_row=jblock-K_row.

Use the interleaved source and target as A_row and B_row, concatenate
all fields in base W, and add J to every supplied field. Every supplied
field is positive, including all-hold histories and identically zero
raw carry or activation fields. All seed, guard, typing, and time
equations follow from the displayed lane formulas.

The supports of A and E are disjoint because E terminates a carry at a
zero source bit. Thus FA+FE<=3J, and the shared slack
alpha=q+J-FA-FE is at least one. Likewise alphaI=W-FI is positive.
Every guard row begins with the k head ones, so FG has unit digit two
even when every counter holds. The seven-field word is native, is below
q^7, and has unit two. The direct ternary mask gives the required
binomial divisibility. Bounds (6) give the hypotheses of the full
parity-free positive Pell converse, which supplies all remaining
positive auxiliaries for this fixed r=P and D0=q^7. Both parities are
covered; no construction of enormous numerical Pell witnesses is
claimed as finite regression evidence.

## 7. Evidence and scope

The exact checker verifies all 85 primitive instructions and all 23
source comparisons, including a symbolic p template. Its finite phase
checks 6,888 positive preliminary tuples, 792 complete power-three
candidates, and 36 accepted histories. It also checks 3,117 canonical
histories for two, three, and four counters, including 232 all-hold
histories and 137 cases with alpha=1. The partial-row counterexample in
Section 1 is checked separately through its exact valuation and all
positive-kernel extension hypotheses.

These finite checks supplement the general proof. The count is fixed
independently of k because p and jblock are fixed numerals, while their
uses as multiplication operands are charged. If k were supplied as an
unknown, this convention would not apply. The endpoint code remains an
explicit interleaving of binary counter bits into ternary positions;
it is not ordinary raw integer input. Routing, zero tests, decrement,
and raw loading need separate counted compositions.

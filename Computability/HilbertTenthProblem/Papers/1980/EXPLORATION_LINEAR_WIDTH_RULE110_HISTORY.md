# A complete 76-operation Rule 110 finite-history certificate

Replacing the fourth-power row width by a linear width reduces the
complete positive finite-history certificate from77 to **76=43M+33A**.
It retains25 positive supplied unknowns and16 equations and recognizes
exactly the same numerical endpoint relation: for positive integers I,F,
both are Boolean radix16 words and a positive number of moving,
zero-exterior Rule110 steps takes16I to16F.

This relation is decidable. The result does not supply the universal
input and halting interface and does not lower the established universal
bound90. Numerals and equality comparisons are free; each multiplication
by a numeral is counted.

The [complete checker](../verification/explore_linear_width_rule110_history.py)
and adjacent JSON verify both the76 source and the75 source obtained by
deleting its stride-divisibility equation. The latter is refuted below
by a full positive false history, including its Pell extension.

## 1. Source and exact saving

Supply positive outer unknowns

    q,A,quot,H,C,Y,J,alphaI

and the unchanged seventeen positive kernel unknowns

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

The code names the outer A `awidth` to avoid collision with the retained
kernel's computed registers. Define

    W=16A, L=q^4, D0=q^6,
    B=16C, T=B+H, U=307C+4Y+J,
    P=T+qY+q^3U,
    M=J(q+1)(4q^2+14).

The six outer equations are

    q=W*quot,
    q-1=H(W-1),
    I+alphaI=A,
    I+WY=C+qF,
    15J=q-1,
    r=(L-P)(L-1)+M.                                      (1)

For completeness, write X=wD0, Z=sD0, Delta=a^2+4a+3 and
u=jc-(2r+1). The ten kernel equations are

    X Z^2 (X Z^2+1) k^2=tau(tau+1),
    c=Zk+eta, k=eta+zeta, k=r+1+hXZ,
    a=Z(X+1), d=X+ac+gamma(4a+3),
    d^2=Delta c^2+1,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u=of-c.                                              (2)

These are the retained fixed-minus43 equations. Their soundness permits
signed computed u and either parity of r; their positive converse applies
at the odd indices constructed below.

The old geometry constructed v*quot, v^2 and W=v^4 in three products.
Here W=16A and W*quot require two products. The input bound is still one
addition, now comparing I+alphaI with A. Every other primitive is unchanged:

| Part | M | A | Total |
|---|---:|---:|---:|
| q^2,L=q^4,D0=q^6 | 3 | 0 | 3 |
| W=16A,W*quot,q-1,W-1,H(W-1) | 3 | 2 | 5 |
| U=307C+4Y+J | 2 | 2 | 4 |
| Input bound | 0 | 1 | 1 |
| Temporal equation | 2 | 2 | 4 |
| B=16C,T=B+H | 1 | 1 | 2 |
| Packing P | 2 | 2 | 4 |
| Mask M | 3 | 2 | 5 |
| Repunit equation, sharing q-1 | 1 | 0 | 1 |
| Index equation | 1 | 3 | 4 |
| Outer subtotal | 18 | 15 | 33 |
| Fixed-minus kernel | 25 | 18 | 43 |
| **Complete source** | **43** | **33** | **76** |

The checker compares all sixteen independently written polynomial
residuals with the schedule. At zero-based index14 it uses only the usual
acyclic correction: source13 times(u^2-y_aux^2). All other comparisons
agree up to the recorded sign. No arithmetic operation is hidden in a
numeral, comparison, or variable power.

## 2. Bounds and mask recovery precede row alignment

From positivity, A=I+alphaI>=2, W>=32, and q>=W. The proof of the
[77 source](EXPLORATION_ONE_FIELD_RULE110_HISTORY.md), Section2, now applies
with the stronger lower bound on W. It uses no radix-alignment conclusion:

    0<M<L,
    r>0 implies P<=L,
    q^3 U<P<=q^4 implies U<q,
    C<q/307, Y<q/4, 256C<q,
    H=(q-1)/(W-1)<q/15,
    T<(16/307+1/15)q<q.

Thus the three actual fields T,Y,U lie below q. The zero q^2 field gives

    P<=q^4-q^3+q^2-1<L,
    q^3<r<q^8.

With proof notation n0=q^3, the unchanged kernel has D0=n0^2,
n0>=64 and n0<r<2n0^3. Its full proof therefore recovers

    X=2^(2r+1), D0 divides binom(2r,r).

In particular q is a power of two. The paid equation15J=q-1 forces
q=16^N for some positive integer N, before the row width is decoded.

The mask has four N-digit blocks with radix16 digits14,14,4,4. Hence
popcount(M)=8N and log2(L)=16N. The complete carry lemma, including
P+M>=L, gives popcount(r)<=24N, with equality exactly when P AND M=0.
Since D0=2^(24N), the kernel forces equality. The already established
bounds extract the fields and prove

    T,Y are Boolean radix16 words,
    every digit of U belongs to {0,1,2,3,8,9,10,11}.          (3)

This step does not require W to be a power of16.

## 3. The initial marker forces the missing row alignment

Since W divides q, write W=2^a. The bound W>=32 gives a>=5.
The divisibility W-1 | q-1 forces a|4N. Thus q=W^t and
H=1+W+...+W^(t-1), for an integer t>=1.

If t=1, W=q is already a power of16. Suppose t>=2. The temporal and
marker equations give the exact identity

    T=16I+16WY-16qF+H.

Reduce modulo16W. Since W is a multiple of16, W^2 is a multiple of16W.
Therefore

    H=1+W modulo16W,
    T=16I+1+W modulo16W.                                  (4)

The input bound is now exactly0<I<A=W/16. Consequently
0<16I+1<W. In (4), the bit at position a is therefore1, without a carry
from the lower part. But (3) permits set bits of T only at positions
divisible by4. Hence4|a. In either case,

    W=16^m, q=16^(mt), m>=2, I<W/16.                       (5)

The alignment is a consequence of the existing typed marker and input
bound. It costs no additional equation or arithmetic operation.

## 4. Actual histories and the full positive converse

The causal argument of the77 proof, Section4, applies verbatim once (5)
is established; it only used the old input bound to obtain I<W/16.
For clarity, its steps are as follows. The temporal equation and C,Y<q
give F<W, then the base-W rows obey

    c_0=I, c_(j+1)=y_j for j<t-1, y_(t-1)=F.

Subtracting the row-start word H from Boolean T makes each row-start
digit of B=T-H belong to{0,14,15}. The first start is zero because
B=16C; the next is zero because I<W/16. Later source rows are Boolean
Y rows, whose high digits are0 or1, so the same subtraction forces every
later start to zero. No borrow remains within a row: B is Boolean.

The bounds256C<q allow both shifted neighbor words, and

    U=J+16B+3B+3C+4Y.

Each local digit lies in[1,12]. The exact scalar table identifies (3)
with Rule110. At row starts Rule110(a,0,c)=c removes the apparent
previous-row dependence; at row ends the next row starts with zero.
The exterior rule Rule110(a,0,0)=0 handles the high boundary. These are
exact zero-exterior moving steps from16I to16F. They also recover
Boolean typing of both numerical parameters I,F.

Conversely, take any genuine positive-height history from16I to16F.
Choose m large enough that I<16^(m-1) and every source and raw-output row
fits with two high blank columns. Set W=16^m,q=W^t,A=W/16,
quot=q/W,H=(q-1)/(W-1),J=(q-1)/15,alphaI=A-I. Pack the source rows
into B and raw output rows into Y, and put C=B/16. All outer unknowns
are strictly positive. The equations, field bounds and exact masks hold.

The index is odd: H and T are odd, q is even, P is odd and M is even.
At this actual index the fixed-minus kernel gives all sixteen remaining
positive witnesses, as specified in Sections5 of the77 proof and
[the positive Life bootstrap](EXPLORATION_LIFE_POSITIVE_BOOTSTRAP.md).
In particular, for I_pell=2r+1 take

    X=2^I_pell, Z=floor((X+1)^(2r)/X^r), w=X/D0, s=Z/D0,
    a=Z(X+1), A_pell=a+2, Delta=A_pell^2-1, P_pell=2XZ^2+1,
    c=psi_(A_pell)(I_pell), d=chi_(A_pell)(I_pell),
    k=psi_(P_pell)(r+1), eta=c-Zk, zeta=k-eta,
    tau=(chi_(P_pell)(r+1)-1)/2, h=(k-r-1)/(XZ),
    gamma=(d-X-ac)/(4a+3).

Choose m_aux=2cI_pell, f=chi_(A_pell)(m_aux),
R_aux=Delta psi_(A_pell)(m_aux), i=R_aux/c^2,
y_aux=psi_(R_aux)(I_pell), u=chi_(R_aux)(I_pell)/R_aux,
j=(u+I_pell)/c and o=(u+c)/f. The retained divisibility, ratio and
odd-index congruence proofs make every listed witness positive integral
and establish all ten equations (2). The new bound still gives
D0<r^2<X, so both scale quotients have exactly the required divisibility.

This proves equality of endpoint predicates with77. It does not assert
an unchanged-witness bijection: a76 witness can use a smaller row width
than permitted by the old bound I<2^m, and enlarging that width changes
the packed index and requires fresh Pell witnesses.

## 5. The 75-operation stride-divisor deletion is false

Deleting q=W*quot removes one multiplication, one equation and quot.
The resulting source has75=42M+33A,24 positive unknowns and15 equations.
Take

    q=16^8=4294967296,
    W=16^6-16^4+16^2=16711936, A=1044496,
    H=257, J=286331153, alphaI=1044240,
    C=1114368, Y=17895680, I=256, F=69633.

All retained outer equations hold. Here T=17830145 and U=700024849
have hexadecimal expansions1101101 and29b98811, respectively, so T,Y
are Boolean and every U digit is permitted by (3). All three fields
are strictly between0 and q. The exact packed index is

    r=96919456642596015541029662201489051854048912785625541435593023378645200076783.

It is odd and has192 set bits, exactly log2(q^6). The range
q^3<r<q^8 and D0<r^2 holds. Therefore the same sixteen fresh positive
kernel witnesses above extend this tuple to a solution of every weakened
equation; no enormous witness is being reused from another index.

Nevertheless it cannot be a moving Rule110 history. I=0x100 has its
lowest live digit at position2, whereas F=0x11001 has one at position0.
The moving rule preserves the lowest occupied position: the raw rule
creates its new leftmost1 immediately to the left of the old leftmost1,
and multiplication by16 moves it back. Positions further left stay zero.
Thus these endpoints are impossible at every positive height. As required,
q is not divisible by W. The complete76 source retains that equation.

## 6. Evidence and scope

The fresh checker verifies both full source ledgers and all31 polynomial
comparisons. Before power decoding it tests160 arithmetic candidates,
including seven non-power q cases with positive index; these are only
bootstrap tests, not full kernel solutions. It checks32,752 initial low
blocks, rejecting all28,387 misaligned cases.

The bounded history enumeration now includes misaligned power-of-two
strides. It examines31,892 Boolean T words, including12,168 with such
strides, and81,993 compatible final words. All37 accepted outer tuples
are actual moving histories. Thirty more canonical histories cover five
inputs and heights1,2,3,4,8,16. Each accepted tuple checks all six outer
equations, strict positivity, field bounds, the full mixed mask, odd
parity, exact binomial valuation and kernel range hypotheses.

The source proof covers arbitrary positive inputs and arbitrary heights;
the tests do not stand in for that proof. Huge Pell coordinates are
specified by the proved converse rather than materialized. The endpoint
predicate remains decidable because the highest occupied digit advances
by exactly one per moving step, determining the only possible height.
The universal frontier remains90.

Review status: author and independent complete proof/source review pass.
Fresh read-only verification exactly matches the saved JSON. The review
covers the complete76 theorem, both source ledgers, the proof order,
alignment and causal arguments, every positive converse formula, and the
full positive extension of the false75 tuple.

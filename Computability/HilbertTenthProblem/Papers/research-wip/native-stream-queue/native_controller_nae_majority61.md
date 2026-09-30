# An exact even-length NAE/majority relation in 61 operations

This complete arithmetic component has **61=33M+28A**, 19 equations
and 26 strictly positive auxiliaries beyond five positive parameters.
It has the cyclic NAE/majority semantics of the
[67-operation component](native_controller_nae_majority67.md), restricted
to even word lengths. Two bounded packed fields suffice. The retained
Pell source itself supplies the parity restriction, so neither a parity
equation nor a square-width equation is added. This remains a finite
relation; the complete universal bound is still 76.

## 1. Exact projection and positive domain

The positive parameters are q,F0,F1,R0,R1. The relation holds exactly
when there are an **even** integer t>=2, offsets 1<=a,b<=t, and Boolean
words d,v of length t satisfying

    q=3^t, H=(q-1)/2, R0=3^a, R1=3^b,
    D=sum_j d_j*3^j, V=sum_j v_j*3^j, d0=1,
    F0=H+D, F1=H+V,
    d_j+(rot_a d)_j+(rot_b d)_j=1+v_j for all j.         (1)

Here `rot_a(d)=(d_a,...,d_(t-1),d0,...,d_(a-1))`, with units digit
listed first. It is a NAE constraint on d and its two rotations, with
v recording their majority. V may be zero. The source supplies positive
H,alpha0,alpha1, the seventeen retained Pell coordinates, and positive
A,B,K0,K1,Z0,Z1. D and V are mathematical decoded words; only D is
computed as a register. There are 31 positive coordinates in total if
the parameters are also existentially selected.

## 2. Exact source and ledger

The outer equations are

    q=2H+1, F0+alpha0=q, F1+alpha1=q,
    r=P=F0+q*F1.                                        (2)

Set the scale D0=q^2. Attach exactly the ten ternary Pell equations in
[the selector proof, Section 2](native_controller_three_selector_53.md),
now using X=wD0,Y=sD0. Their main parameter is A_main=a+3, their
discriminant is Delta=a^2+6a+8, and their positive auxiliary branch is

    u=2r+1+jc=c+of.                                    (3)

The field/routing equations are

    A+B+D=F1,             D=F0-H,
    R0*A=D+2H*K0,         q=R0*Z0,
    R1*B=D+2H*K1,         q=R1*Z1.                     (4)

As in the 67 source, D is a computed register and contributes no
additional equation. The seven outer instructions are

    twice_H=H+H; q_calc=twice_H+1;
    bound0=F0+alpha0; bound1=F1+alpha1;
    p0=q*F1; P=F0+p0; D0=q*q.

They cost 2M+5A. The retained core costs 25M+18A and the eleven
instructions implementing (4) cost 6M+5A, for 61=33M+28A. Equality
comparisons are free. In particular the source contains no instruction
`r=2*nu` or `q=n*n`. The [checker](native_controller_nae_majority61.py)
expands all 19 source polynomials at this q^2 scale and verifies the
usual acyclic auxiliary-norm correction independently of the schedule.

## 3. Preliminary bounds without digit or parity assumptions

Positivity gives H>=1, q odd with q>=3, 1<=Fi<=q-1 and

    q+1<=r<q^2=D0<r^2.                                 (5)

The whole source cannot have q=3. In that case H=1 and F0,F1 belong
to {1,2}. If F0=2, then D=1 and the gate requires A+B=F1-1<=1,
contradicting A,B>0. If F0=1, then D=0; the gate forces F1=2 and
A=B=1. But R0 divides 3, whereas its transport reads R0=2K0,
again impossible. This argument uses only (2) and (4).

Consequently q>=5, D0>=25 and r>=6. Before recovering any powers,

    X,Y>=D0, XY>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<6/(D0+1)<=6/26<1/2.                           (6)

These bounds verify the retained kernel argument as follows. Its first
Pell index n is at least r+1. Since the first base exceeds A_main and
c>Yk>k, the main index p is at least n+1>=r+2>=8. Thus

    c>A_main^7>A_main*Delta^2, c>2p and c>2r+1.

The generic auxiliary-rank and half-parameter arguments therefore
recover p=2r+1. The first index is n=r+1 because the unchanged
base comparison has positive difference

    4Y(X(Y-1)-1)-11>0.

All these steps precede any use of parity. The ratio proof at (6),
with xi=(X+1)^(2r)/X^r, gives

    xi<c/k<xi(1+12r/a),
    Y>=X^r, a>X^(r+1), 0<c/k-xi<24r/(X+1).

The direct ternary recurrence yields X congruent to 3^(2r+1) modulo
6a+8. Both representatives are positive and below that modulus, since
X<a and `3*9^r<X^(r+1)<a` for X>=25. Hence X=3^(2r+1) exactly,
and q^2 dividing X makes q a power of three. Then X>48r; the ratio
error is below 1/2 and the binomial tail below 1/6. The unit interval
gives

    Y=floor((X+1)^(2r)/X^r), q^2 divides binom(2r,r).     (7)

This explicitly checks the smaller thresholds; it does not import a
larger lower bound on r or assume parity in the index argument.

## 4. Kernel parity, typing and the even length

The [generic signed-parity theorem, Section 4](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
applies to (3), with its **positive** sign. To check every hypothesis,
we already have p=2r+1, c=psi_(A_main)(p)>2p, and the retained relaxed
auxiliary classification gives

    f=chi_(A_main)(m), c divides m, m>=2p,
    R=ic^2>1, c divides R, R^2=Delta(f^2-1).

In particular f>=chi_(A_main)(2p)=1+2Delta*c^2>2c. Also u>0 and
the source gives u=p modulo c and u=c modulo f. The signed theorem
therefore yields `(-1)^((p-1)/2)=+1`, or **r even**, for every positive
source solution. This is a necessity theorem for arbitrary auxiliary
indices, not an assumption about the canonical converse.

Write q=3^t. The paid field bounds make P=F0+qF1<q^2 a genuine
two-chunk packing. By (7), doubling P in ternary gives at least 2t
carries, the maximal possible number. Its units trit must be 2 and
all remaining 2t-1 trits must be 1 or 2. Thus both fields have native
trits in {1,2}, and F0's units trit is 2. Subtracting H gives Boolean
D,V with D's units digit 1.

The bound from the gate is now

    0<A,B<A+B=H+V-D<=2H-D<q-1.

Exactly the argument in Section 3 of the 67 proof recovers
R0=3^a,R1=3^b with 1<=a,b<=t, identifies A,B as the stated rotations,
and makes the gate coefficientwise because its residuals are in
[-2,2]. No port typing was assumed before this bound.

Rotating ternary digits preserves the represented integer modulo 2.
Therefore A=B=D modulo 2. The gate gives D+V=H modulo 2, and the
packed index satisfies

    r=F0+qF1=F0+F1=D+V=H modulo 2.

Since the kernel forces r even, H is even. For q=3^t, this is
equivalent to t even. All semantics (1) have now been proved.

## 5. Converse and nonempty examples

Given (1), set alpha_i=q-Fi. Since 0<=D,V<=H and H>=1, both fields
lie in [H,2H] and the slacks are positive. The units digit condition
makes P have 2t native trits and units trit 2, so (7)'s divisibility
holds. The coefficientwise gate and rotation parity give
P=D+V=H=0 modulo 2 because t is even.

The retained constructive positive plus-branch converse, as spelled out
in [the Boolean-pairs proof, Section 5](native_controller_boolean_pairs56.md),
now uses this r and D0=q^2. Conditions (5)--(7) give exactly its scale,
growth, divisibility and even-index hypotheses. In particular
2r+1>=2t ensures w=X/D0 is integral, and (7) makes s=Y/D0 integral.
Every other main, first-Pell and auxiliary coordinate is supplied by
that same positive map. Set A,B to the rotations, K0=D mod 3^a,
K1=D mod 3^b, and Z0=3^(t-a),Z1=3^(t-b). These are all positive,
and division with remainder verifies (4).

For example take t=2,d=(1,0),a=b=1,v=(0,1). The positive outer tuple is

    q=9,H=4,F0=5,F1=7,alpha0=4,alpha1=2,r=68,
    R0=R1=3,A=B=3,K0=K1=1,Z0=Z1=3.

The t=2,a=2,b=1 example instead has v=(1,0),F1=5,r=50 and an identity
port. A zero-majority example has t=6,d=(1,1,0,0,0,0),a=2,b=4.
Thus the even-length restriction leaves a nonempty relation, including
zero decoded majority and identity rotations.

## 6. Evidence and scope

The [receipt](native_controller_nae_majority61.json) checks 295,236
bounded positive field tuples before power recovery, all four positive
q=3 outer candidates, and exact valuation/typing equivalence on all
65,708 field tuples through t=5. A separate Boolean implementation
checks 503,805 word/offset candidates through t=12: 10,599 even-length
NAE cases remain, while 5,190 odd-length NAE cases have the parity
excluded by the proved kernel theorem. Every admitted even-length
point through t=8 is lifted to the literal positive outer source.

For the actual r=50 and r=68 examples, exact main/first Pell norms,
positive interval slacks, rounding and scale divisibility are checked
numerically. The much larger auxiliary extension is proved parametrically.
The source does not numerically classify arbitrary Pell solutions; its
parity step uses the independently established signed theorem.

Run `python native_controller_nae_majority61.py` for a fresh comparison
with the receipt. The remaining input, geometry and acceptance needed
for a universal simulation are not supplied by a six-row truth table.
Independent complete proof/source review and fresh default-receipt replay
passed, including the conditional spectral appendix below. No findings
were reported.

## 7. A structural restriction under an additional rotation closure

This section is conditional: the 61 source does **not** require v to
be a rotation of d. Suppose a proposed composition additionally imposes
`v=rot_e(d)`. Set s_j=2d_j-1 and let R_h act by shifting a vector's
j-th coordinate to its `(j+h) mod t` coordinate. The exact gate is
then the linear equation

    (I+R_a+R_b-R_e)s=0.                                 (8)

Summing coordinates gives sum(s)=0, so d has exactly t/2 ones.
For more detail, expand s in the finite Fourier basis `z^j`, where
z runs through the complex t-th roots of unity. Any mode with nonzero
coefficient satisfies

    1+z^a+z^b=z^e.

Put x=z^a,y=z^b. All these powers have modulus one, and the exact
identity

    xy*(|1+x+y|^2-1)=(1+x)(1+y)(x+y)

shows that every supported mode belongs to at least one of three sets:

    z^a=-1 and z^e=z^b;
    z^b=-1 and z^e=z^a;
    z^a=-z^b and z^e=1.                                 (9)

The displayed identity is interpreted using conjugate(x)=1/x and
conjugate(y)=1/y; the checker verifies it as a Laurent-polynomial
identity. Since Fourier modes diagonalize every cyclic shift, (9)
implies the exact annihilating relation

    (I+R_a)(I+R_b)(R_a+R_b)s=0.                         (10)

This is a restriction on spectral support. It does not assert that
the entire Boolean word uses just one cancellation alternative in (9).
For an explicit mixed example, let t=60,a=6,b=16,e=40. On the even
coordinates `j=2k`, put d_j=1 exactly when k modulo 6 is below 3;
on the odd coordinates `j=2k+1`, put d_j=1 exactly when k modulo 10
is below 5. The even coordinates use the first cancellation, and the
odd coordinates use the third. Equation (8) holds, but none of the
three pairs `(d,R_a d)`, `(d,R_b d)`, `(R_a d,R_b d)` is globally
complementary. The checker verifies this construction directly.
Nor does it give a uniform bound on the amount of freely selectable
data: for any m>=1, let t=2m, a=m, e=b and choose any first half of d
starting with 1, followed by its complement. Then R_a s=-s, so (8)
holds for every b. There are 2^(m-1) such words. They represent a
copy/complement family; their existence supplies no universal simulation.

The additional receipt checks (10) and balanced population on every
admitted closure through t=12, independently of the Fourier argument,
and checks the free-half family through m=8. This conditional lemma
is structural only. No decision procedure for a larger arithmetic
architecture, or universality obstruction for arbitrary extensions,
is inferred from it.

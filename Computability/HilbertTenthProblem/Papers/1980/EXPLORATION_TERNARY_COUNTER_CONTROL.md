# Ternary Boolean carry cells with a shared termination signal

This note gives a three-addition local component and a one-addition raw
ternary input relation. It does not construct a complete universal history
certificate. In particular, the binary significance of a Boolean counter
track and the native ternary significance of the raw input are distinct.

## 1. An exact three-addition control split

Let A,B,C,D,E be aligned Boolean words in radix three. Interpret A as a
counter bit before an update, B as the bit afterwards, C as an active
incoming carry, D as its continuation and E as its termination signal.
The increment component is

    C=D+E,
    A+E=B+D.                                       (1)

Every raw digit on either side is at most two. Consequently equality of
the integers is equivalent to both equations at every digit; no signed
carry assumption or inequality is needed. At one cell, (1) has the unique
solution

    D=A*C, E=(1-A)*C, B=A XOR C.

Thus an inactive cell is unchanged. An active zero becomes one and emits E;
an active one becomes zero and emits D. The schedule is the three additions
D+E, A+E, B+D, followed by two equality tests.

For borrow propagation, use instead

    C=D+E,
    A+D=B+E.                                       (2)

It has the unique solution

    D=(1-A)*C, E=A*C, B=A XOR C.

An active zero becomes one and continues the borrow; an active one becomes
zero and terminates it. Again the cost is exactly three additions.

This is an alternative to the ternary half-adder repair using a Boolean
OR helper T=B+D. Here the extra field E is the event that can activate the
next machine instruction when the ripple terminates. A complete machine
may be able to reuse that signal for control, but no such reuse is counted
before its incidence and temporal equations are supplied.

For comparison, the direct equation A+C=B+2D is not an exact packed
ternary half-adder. The Boolean ternary words A=12,C=9,B=1,D=10 satisfy
it: 12+9=1+2*10. At the unit position they have a=c=0,b=d=1, which is not
a half-adder assignment. Equations (1) avoid this example because C=D+E
with Boolean E enforces disjoint D,E and hence digitwise D<=C. After that
substitution, both sides of the remaining equation have the raw bound two.

## 2. Which wiring remains necessary

In a finite ripple chain the outgoing control at cell j must be the
incoming control at cell j+1. If C,D are the corresponding packed words,
the identity for a chain of length m with initial carry one is

    C=1+3D-d_final*3^m.                            (3)

Its boundary term is not optional. Multiple registers and multiple time
rows need their own seed and boundary words, linked by counted equations.
The signal E has at most one occupied cell along an actual active ripple,
but equations (1) or (2) alone do not establish that global fact. It follows
only after the chain and its unique initial activation have been enforced.

Likewise, (2) supplies the arithmetic of a decrement ripple, not the full
conditional-decrement instruction. To recognize a zero register, the
machine must observe the final outgoing borrow at its high end and choose
the correct program successor. To increment without finite overflow, the
chosen width must have a blank high bit and the soundness proof must enforce
that boundary. Boolean masks, positive representations of zero fields,
register selection and accepting control remain separate obligations.

## 3. A native ternary query splits into two Boolean words

Every nonnegative integer x has a representation

    x=I0+I1,                                      (4)

with I0,I1 Boolean in radix three. At each digit, split zero as 0+0,
two as 1+1, and one as either 1+0 or 0+1. Every raw coefficient is at
most two, so the integer equation has no carries and exactly describes
these splits. It costs one addition. A query with s ternary digits equal
to one has exactly 2^s ordered representations; uniqueness is not claimed.

The pair represents the native ternary digit by its sum. A machine using
this input must therefore interpret the two tracks by that sum, tolerate
both encodings of digit one, or enforce a canonical encoding separately.
It cannot treat I0 and I1 as the even and odd binary bits of x. The formula
x=I0+2I1 would not represent arbitrary x by ternary Boolean words without
carry ambiguities, unlike the previously proved radix-four input link.

In particular, feeding (4) into the binary ripple cells of Section 1 does
not yet load the raw number into a binary counter. A Boolean word
sum a_j*3^j has native ternary value sum a_j*3^j, whereas those cells treat
its sequence of bits as the binary counter sum a_j*2^j. The input conversion
or a native ternary-counter control system is still an explicit missing
part of a universal construction.

If a surrounding mask already certifies positive native words
Fi=J+Ii with ternary digits one or two, where J=(q-1)/2 and q=3^m, then
the direct positive input link is

    F0+F1=x+(q-1).                                (5)

When q-1 is already available, this costs two additions. The range and
mask proof that certifies those native words, and any construction of J,
are not supplied by (5).

## 4. A four-field ripple and its automatic parity

For one ripple starting at the low end, Boolean fields D,E can absorb C.
Suppose all fields are nonnegative Boolean ternary words below q=3^m.
Impose

    E=2D+1,
    A+E=B+D                                       (6)

for increment, or replace the second equation by A+D=B+E for borrow.
The schedule has four operations: 2D, 2D+1, and the two side additions.
Only A,B,D,E need masks. This is an exact bounded ripple relation, not
just a loose global addition.

Indeed E=2D+1 forces

    D=(3^k-1)/2, E=3^k, 0<=k<m.                  (7)

This notation describes the decoded witnesses; the certificate does not
compute a variable exponent. In the unit digit, D=1 makes 2D+1 produce
zero and carry one, while D=0 makes it produce one and no carry. During
that carry, another D digit one again produces zero and continues it.
At the first D zero, E receives a one and the carry ends. Thereafter any
D one would produce the forbidden E digit two. Since D is finite, such
a first zero exists, and E<q ensures k<m. This proves (7).

Thus D and E are disjoint, C=D+E is Boolean, and C=1+3D. Equations (6)
therefore imply the exact cell equations (1) with their correct wiring.
Equivalently, the low k bits of A are one and become zero, its bit k is
zero and becomes one, and all higher bits agree with B. For borrow those
low bits are zero and become one, and bit k changes from one to zero.
The hypotheses exclude increment overflow and decrement from zero.

There is a useful parity identity for either mode:

    A+B+D+E is even.                               (8)

For increment it equals 2(A+E); for borrow it equals 2(A+D). Since q is
odd, any four-field Horner word using precisely A,B,D,E has the parity
of their sum. Hence it is even without a separate parity equation. In
the proposed odd-prime mask r=D0-3P-1 with odd D0, r is consequently even
as well. This observation does not require q to be a power of two or a
zero unit digit in the first field.

If the four supplied fields are instead native positive words
FA=J+A, FB=J+B, FD=J+D, FE=J+E, the side-sum equation and parity still
hold directly: the offsets cancel, and four copies of J have even sum.
The ripple seed equation becomes FE+J=2FD+1. With J already available
it costs three operations, not two, so the corresponding native local
schedule costs five operations. Any sharing that removes that extra
operation, or computes J, requires a separate counted construction.

## 5. Bounded exact evidence

The companion `../verification/explore_ternary_counter_control.py` checks
every scalar assignment for both local relations, every two-cell assignment,
and complete finite ripple chains. Its input phase enumerates every pair
of Boolean tracks through seven ternary digits and verifies that the
multiplicity of a represented x is exactly 2 to the number of its digits
equal to one. The native-positive link is checked on the same complete
range. The direct-half-adder counterexample is also checked explicitly.
The four-field phase checks the complete possible D words through eight
digits, the classification (7), both bounded ripple directions and the
even parity of all accepted packed words, including native offsets.

The evidence concerns these local and input lemmas. It gives neither an
operation count for a complete universal machine nor a new universal bound.

# A complete cyclic NAE/majority relation in 67 operations

This arithmetic component has **67=36M+31A**, 19 equations and 24
strictly positive auxiliaries beyond seven positive parameters. It
combines the reviewed [two Boolean pairs](native_controller_boolean_pairs56.md)
with two cyclic rotations and the six-row relation in which three input
bits are not all equal and a fourth bit records their majority. It
includes the native base-three geometry and positive Pell extension.
Ordinary-input initialization, accepting states and a universal compiler
are not included. The established complete universal bound remains 76.

## 1. Exact projection

For a bit word `d=(d0,...,d_(t-1))`, indexed from its units digit, define

    word(d)=sum_j d_j*3^j,
    rot_a(d)=(d_a,...,d_(t-1),d0,...,d_(a-1)).

Offsets may equal t, giving the identity. The seven positive parameters
are q,F0,F1,F2,F3,R0,R1. They admit the arithmetic witnesses exactly
when there are t>=1, offsets 1<=a,b<=t, and Boolean words d,v such that

    q=3^t, H=(q-1)/2, R0=3^a, R1=3^b,
    d0=1, D=word(d), V=word(v),
    (F0,F1,F2,F3)=(H+D,2H-D,H+V,2H-V),
    d_j+(rot_a d)_j+(rot_b d)_j=1+v_j for every j.       (1)

The last condition says the three bits have sum 1 or 2, and v_j is 1
exactly when that sum is 2. Thus it is the not-all-equal (NAE) constraint,
with its majority bit also supplied. Although t=1 is harmless in the
statement, (1) has no such solution. V can be zero, and either offset
can give an identity rotation. No zero decoded word is supplied as a
positive existential coordinate.

## 2. Literal source and count

Retain all 56 instructions, 14 equations and 18 auxiliaries of the
Boolean-pairs source. In particular H (`Hrep`) and 2H (`twice_H`) are
already computed, q=2H+1, and r packs its four fields at scale q^4.
Add positive auxiliaries A,B,K0,K1,Z0,Z1 and five equations

    A+B+D=F2,                   D=F0-H,
    R0*A=D+(q-1)K0,             q=R0*Z0,
    R1*B=D+(q-1)K1,             q=R1*Z1.                (2)

Here D is a computed register, not an additional equation or supplied
coordinate. The literal extra schedule is

    D=F0-H; ports=A+B; gate=ports+D;
    RA0=R0*A; guard0=twice_H*K0; rhs0=D+guard0;
    div0=R0*Z0;
    RA1=R1*B; guard1=twice_H*K1; rhs1=D+guard1;
    div1=R1*Z1.

Its comparisons are `gate=F2`, `RAi=rhsi`, and `q=divi`. The 11
additional operations are 6M+5A, giving 67=36M+31A. The supplied
majority field F2 already equals H+V; computing V or recomputing H+V
would be unnecessary. There are 19 equations and 24 positive
auxiliaries, or 31 positive coordinates when all parameters are also
chosen existentially.

The [source](native_controller_nae_majority67.py) imports the frozen
56 schedule, expands all 19 polynomials independently, and checks the
retained auxiliary-norm substitution by its exact acyclic correction.
It audits every supplied coordinate and the full literal ledger.

## 3. Soundness, including arbitrary positive ports

The Boolean-pairs theorem first gives q=3^t, H=(q-1)/2 and Boolean
words D,V with D's units digit 1. Thus 1<=D<=H and 0<=V<=H, while
F2=H+V. Equation (2) implies

    A+B=H+V-D<=2H-D<q-1.

In particular both positive ports are strictly below q-1. The bound
was derived before assuming either port is a Boolean word.

Factorization of q gives R0=3^a for 0<=a<=t. If a=0, its transport
would give A=D+(q-1)K0>q-1, a contradiction. Therefore 1<=a<=t.
Write D=R0*u+l with 0<=l<R0. Since D has units digit 1, l>0.
The integer

    Astar=u+(q/R0)*l

is the Boolean word `rot_a(d)`, satisfies 0<Astar<=H<q-1 and
`R0*Astar=D+(q-1)l`. Because R0 is coprime to q-1, transport makes
A congruent to Astar modulo q-1. Their strict bounds imply A=Astar,
and the exact equality then gives K0=l. The same argument gives
B=word(rot_b(d)) and K1=D mod R1. It also covers offset t, when
the rotation is the identity and its positive quotient is D.

Now expand `A+B+D=H+V` in base three. Its residual at each position
is in [-2,2]. A nonzero least residual cannot be divisible by three;
successive reduction modulo three therefore forces every residual to
be zero. This proves exactly (1), including the majority relation.

## 4. Positive converse

Given (1), all four Fi are positive and satisfy the Boolean-pairs
semantics. That theorem supplies all 18 strictly positive auxiliaries,
including the retained 43-operation Pell kernel. Set

    A=word(rot_a(d)), B=word(rot_b(d)),
    K0=D mod 3^a, K1=D mod 3^b,
    Z0=3^(t-a), Z1=3^(t-b).

D is nonzero, so its rotations A,B are positive. Its units digit is 1
and a,b>=1, so K0,K1 are positive. Both Z coordinates are positive,
including when an offset equals t. Rotation division and (1) verify
all five added equalities. The positive Pell witnesses are inherited
from the parametric converse, not from an assertion that their enormous
full numerical tuple has been materialized.

For a concrete nonempty example take t=2, d=(1,0), a=b=1 and v=(0,1).
Then

    q=9, H=4, (F0,F1,F2,F3)=(5,7,7,5),
    R0=R1=3, A=B=3, K0=K1=1, Z0=Z1=3.

Every displayed coordinate is positive; the packed index is r=4280.
The example t=3, d=(1,0,0), a=1,b=2 has v=(0,0,0), illustrating
that zero majority is permitted. The checker also includes an identity
rotation example with t=2,a=2,b=1.

## 5. Evidence and limits

The [receipt](native_controller_nae_majority67.json) records an
exhaustive test of 1,611,894 arbitrary positive port tuples through
t=5, with 99 admitted tuples. Those ports are not assumed Boolean
during the arithmetic test. A separate bit-word implementation checks
503,805 word/offset candidates through t=12, including 15,789 admitted
ones, and lifts every admitted point through t=8 to the positive outer
equations and the required packed binomial valuation. The six local
rows, zero majority and identity rotations are explicitly checked.

Run `python native_controller_nae_majority67.py` to compare a fresh
result with the saved receipt. The unchanged complete typing theorem
and Section 4 supply the unbounded positive Pell extension. The finite
tests supplement these proofs; they do not prove a universal simulation.
In particular the rotations commute as permutations, and this note
does not infer either universality or a general decision procedure from
the local NAE truth table. Independent complete proof/source review and
fresh default-receipt replay passed with no findings.

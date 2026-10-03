# Native nonlinear composition: paid routing and its uniform-wiring limitation

The complete 53/54-operation selector relation supplies a nonlinear native
gate without another mask kernel. This note closes a useful arithmetic
routing interface: **66=35M+31A** proves a finite cyclic NAND relation,
including both input rotations and their typing; **67=35M+32A** proves
each of 54 fixed finite three-state rule variants. These are not universal
certificates. The uniform two-rotation NAND relation has an explicit
structural collapse, so a universal compiler still needs different wiring
or a different local state model.

The dependency is the reviewed
[three-selector module](native_controller_three_selector_53.md). Its
53-operation version has no supplied repunit; this composition deliberately
uses the 54-operation version with positive H and q=2H+1.

## 1. The native nonlinear gate

Write Fi=H+Ti with true one-hot Boolean selectors Ti. Define

    D=2H-F2=H-T2,
    S=H+F2-F0=H-T0+T2.                                  (1)

The local trit of S is 0, 1 or 2 according to the selected label, and
the corresponding Boolean digit of D is 1, 1 or 0. If Boolean words
A,B satisfy A+B=S, then D is their digitwise NAND. Both sides have
uncarried digits in {0,1,2}. Equivalently

    A+B+T0-T2=H

has local residuals in [-2,2], which also proves equality digit by digit
by looking at the first nonzero residual. Booleanity of A and B cannot
be omitted from this argument; Section 2 derives it from paid routing.

The 54 module already computes 2H. Thus (1) takes three additions or
subtractions, and computing A+B costs one more. This is a 58-operation
gate relation conditional on the input words' Boolean typing and common
length. D is a derived register, not an extra positive supplied witness.
The fixed first selector is 0, so the units digit of D is 1.

## 2. Both Boolean input words can be recovered from rotation equations

Supply positive A,B,R0,R1,K0,K1,Z0,Z1 and impose

    A+B=S,
    R0*A=D+(2H)*K0,       q=R0*Z0,
    R1*B=D+(2H)*K1,       q=R1*Z1.                       (2)

No Boolean input masks or separate A/B bounds are assumed. Since S<=2H
and A,B are positive, (2) first gives

    0<A,B<2H=q-1.

The selector module has already proved q=3^t. Each positive divisor Ri
of q is therefore 3^ai for 0<=ai<=t. It is invertible modulo q-1. The
rotation equation uniquely specifies the corresponding input word as
the cyclic right rotation of D by ai native trit positions: writing
D=K+Ri*tail gives

    rotate(D)=tail+(q/Ri)*K,
    Ri*rotate(D)=D+(q-1)*K.

The displayed positive range selects this unique residue. The genuine
rotation is Boolean, nonzero and at most H, because D has those
properties. Therefore A and B have their claimed typing, and Section 1
applies without circularity.

Positivity of Ki excludes ai=0. It causes no missing rotation: ai=t
represents the identity, and K=D>0. For 1<=ai<t, the true K is the
lowest ai-trit prefix of D. Its units digit is 1, so K>0. Zi=q/Ri is
also positive. Thus every cyclic NAND solution with the selected
starting label has all positive witnesses required by (2).

Precisely, for positive parameters q,F0,F1,F2,R0,R1, this full relation
has witnesses exactly when the selector predicate holds, Ri=3^ai with
1<=ai<=t, and the word D from (1) is the digitwise NAND of its two
cyclic right rotations by a0,a1, whose digitwise input count is S.
The first selected label 0 additionally requires both rotated inputs to
be zero at position 0. This restriction is part of the relation; it is
not true of every abstract cyclic NAND fixed point.

There are twenty-four positive auxiliaries: the eighteen of the 54 module
and A,B,K0,K1,Z0,Z1. The full source has eighteen equations. Appending
these twelve instructions to the 54 schedule implements all additions:

    D=twice_H-F2; S1=H+F2; S=S1-F0; ports=A+B;
    RA0=R0*A; guard0=twice_H*K0; rhs0=D+guard0; div0=R0*Z0;
    RA1=R1*B; guard1=twice_H*K1; rhs1=D+guard1; div1=R1*Z1.

Compare ports=S, RAi=rhsi and q=divi. These are 6M+6A, making the
full count 66=35M+31A. No power, digit conversion, routing bound or
input-word typing is free in this finite relation. Ordinary raw-input
initialization and a universal accepting computation remain absent.

## 3. Why uniform cyclic NAND wiring is insufficient

Let P,Q be any commuting permutations of a finite set of positions.
Suppose a Boolean vector d satisfies d=NAND(Pd,Qd). Substituting the
same relation into both input words gives, by Boolean algebra,

    d = PQd AND (P^2d OR Q^2d).

Hence d<=PQd coordinatewise. A permutation preserves the number of one
entries, so this inequality must be equality:

    d=PQd.                                                  (3)

For the two cyclic rotations, d is invariant under their composed
rotation. On the quotient by that rotation, Q=P^(-1), and the remaining
condition is just

    d_j=NAND(d_(j-1),d_(j+1))

on each P-cycle. Its zeros are isolated and its runs of ones have length
one or two: it is a cyclic concatenation of blocks 01 and 011. This
gives a concrete structural obstruction to treating this homogeneous
NAND lattice as an arbitrary serialized NAND network. The gate's
functional completeness does not certify a wiring compiler.

This conclusion is about commuting permutations and all-position cyclic
NAND constraints. It does not cover noncommuting incidence, open boundary
conditions, periodic gate types, additional state projections or other
nonlinear local relations.

## 4. A richer three-state rule class remains available

The selectors also support two *different* Boolean projections of their
three-state word. A projection with units digit 1 is one of

    F0-H,       2H-F1,       2H-F2.

Each takes one subtraction and supplies a positive Boolean word with a
positive low prefix for every nonempty rotation. Choose fixed Boolean
maps alpha,beta from (1,0,0), (1,0,1), (1,1,0), and a fixed permutation
pi of the three labels. This gives 3*3*6=54 source variants. Let W0,W1
be the corresponding projections and put

    S=H+F_pi(2)-F_pi(0).

Supply the same positive parameters and auxiliaries as in Section 2 and
impose

    A+B=S,
    R0*A=W0+(2H)*K0,       q=R0*Z0,
    R1*B=W1+(2H)*K1,       q=R1*Z1.                    (4)

The 54 module proves W0,W1 Boolean, each nonzero with units digit 1,
and 0<=S<=2H. Therefore Section 2's bound and unique-rotation argument
applies to each input independently. It follows that (4) holds exactly
for native label words c_0,...,c_(t-1), c_0=0, and offsets 1<=a,b<=t
such that R0=3^a, R1=3^b and

    c_j=pi(alpha(c_((j+a) mod t))+beta(c_((j+b) mod t)))

at every position j. Conversely every such word has positive A,B and
the positive prefix witnesses K0,K1 described in Section 2, together
with the positive witnesses of the selector module. This proves a
complete finite cyclic relation for each fixed variant. It does not
implement an arbitrary choice of alpha,beta or pi as additional inputs.

The literal added instructions are

    W0=chosen projection; W1=chosen projection;
    S1=H+F_pi(2); S=S1-F_pi(0); ports=A+B;
    RA0=R0*A; guard0=twice_H*K0; rhs0=W0+guard0; div0=R0*Z0;
    RA1=R1*B; guard1=twice_H*K1; rhs1=W1+guard1; div1=R1*Z1.

Each projection line is exactly one of the three subtractions listed
above. The additional cost is 6M+7A, making **67=35M+32A**. There are
18 equations and 24 positive auxiliaries, with the same six positive
parameters as the 66 relation. The source checker expands all 54 literal
variants against independent polynomials. For a complement projection,
the expanded source differs by the existing selector checksum
F0+F1+F2-4H; this explicitly recorded triangular correction does not
introduce another equation or arithmetic instruction.

On an open one-way cellular grid the corresponding local table has form

    f(left,right)=perm(alpha(left)+beta(right)).             (5)

where alpha,beta map the three states to bits. There are 147 distinct
tables when all Boolean maps and all six output permutations are allowed.
The checker exhaustively tests the following narrowly specified Rule 110
embedding: encode each bit by a distinct length-m ternary block, iterate
(5) for exactly 2m steps, and require every encoded binary triple to
produce the encoding of its Rule 110 update. No embedding occurs for
m=1,...,6. This is only a bounded negative search. Other block sizes,
time scalings, backgrounds, simulations or universal machine models remain
open. Some Boolean projections in this search may vanish on an entire
word; their strictly positive arithmetic adaptation is not included in
the 67 ledger above. No universality proof is supplied for any table.

This is a substantive missing step, not an assumption that a small rule
must be universal. The 2025 primary survey by Baburin, Cook, Groetschla,
Plesner and Wattenhofer describes the known three-state one-way
synchronous candidate as still lacking a universality proof; its
three-state asynchronous universal construction uses the larger von
Neumann neighborhood. See Section 5 of
[Universality Frontier for Asynchronous Cellular Automata](https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.11/LIPIcs.MFCS.2025.11.html).
That dated literature observation does not prove nonuniversality of (5).

## 5. Direct three-label queue projections have a separate restriction

Suppose every selector label has one fixed removed/appended symbol pair.
To process unrestricted ordinary ternary digits in a single coordinate,
all three removed symbols 0,1,2 must appear. With only three labels, each
removed symbol then has a unique appended symbol f(a), independent of
the control state. For a fixed physical queue length m, every full turn
applies f coordinatewise to the queue. After n turns its content is
f^n applied to its initial word, with the ordinary cyclic shift between
turns. The controller can admit or reject portions of this predetermined
content orbit, but cannot choose a different rewrite for the same symbol.

Fixed-length padding or serial codes do not change this conclusion when
each physical step still uses exactly those three fixed pairs. The actual
two-coordinate delayed loader additionally needs more than three distinct
removed symbols, including its delimiter. State-dependent read/append
projections or a larger label relation would be substantive extensions.
This observation is stated at each fixed queue length; no undecidability
or uniform-language classification over all existential padding lengths
is being assumed from it.

## 6. Evidence boundary

The checker independently verifies the complete 66 schedule and all
eighteen polynomial comparisons, including the inherited auxiliary-norm
correction, and all 54 complete 67 source variants with their explicit
checksum corrections. It enumerates finite selector/rotation candidates
with arbitrary positive input words, checks the commuting-permutation identity
on all bounded Boolean cycles, and performs the specified block-code
search. Default execution compares its saved receipt; `--write` writes it.
The 53/54 dependency is not edited. These are mathematical component
proofs and finite checks, not a complete universal certificate.

Two independent complete scoped proof/source reviews pass for the 66 source
and all 54 literal 67 variants, including their positive converse, source
corrections and evidence boundaries. Fresh default receipt replay matches.

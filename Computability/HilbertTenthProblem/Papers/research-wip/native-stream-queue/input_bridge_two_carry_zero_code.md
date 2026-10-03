# Two independent carries cannot strengthen the same zero-code Rule110 embedding

The [Boolean60 source](input_bridge_boolean_ternary60.md) leaves enough
operations for two zero-offset affine carry equalities. A natural proposal
is to lengthen the existing00/12 serialization and use a second independent
carry equation to remove its extra paths. The following exact obstruction
rules out that specific direct construction at **every block length**.

Suppose logical0 is the all-zero ternary block and logical1 is one fixed
nonzero block used for both reads and appends. Realize each of the six
Rule110 scan transitions by a fixed choice of Boolean read/append rail
words, shared by all carry coordinates. If those six transitions have
three distinct encoded control states, the allowable affine carry
coefficient vectors span a space of dimension at most one. Two independent
vectors would make **all three states coincide**.

This is not a general nonuniversality theorem. State refinements,
phase-dependent encodings, different read/write codes, a nonzero logical
zero, and other local relations are outside the statement. It identifies
an obstruction to a proposed extra filter, not a lower bound for every
possible controller. The established complete universal bound remains76.

## 1. General setup and elimination of the states

Let the block length be ell>=1, set R=3^ell, and let logical1 have scalar
word C with1<=C<R. A Boolean rail word has ternary digits0/1 and is at most
H=(R-1)/2. Every read or append realization of C is a pair(v,C-v) of such
words. Logical0 has the unique rail realization(0,0).

For one carry coordinate write its step relation as

    3k_next=k+h+r0*d0+r1*d1+a0*p0+a1*p1.

The logical A/read0/write0/A loop forces h=2*k_A. Translate the carry by
k_A; the offset then becomes zero, and the encoded A state becomes0.
Thus allowing constant offsets provides no extra coefficient direction.
After ell microsteps, a block transition has

    R*k_target-k_source = read_weight + append_weight. (1)

The six desired logical transitions are

    A0/0A, A1/1B, B0/1A, B1/1C, C0/1A, C1/0C.

Choose first read-rail words uA,uB,uC for the three read1 edges, in their
listed source states. Choose first append-rail words vA,vB,vC,vD for the
four write1 edges A1, B0, B1, C0, respectively. The two zero-read edges
eliminate the translated states:

    b=-append_weight(vB,C-vB),
    c=-append_weight(vD,C-vD).                          (2)

Use the invertible coefficient coordinates

    alpha=r0-r1, beta=r1, gamma=a0-a1, delta=a1.

The other three nontrivial edges now give a homogeneous system Mz=0,
where z=(alpha,beta,gamma,delta) and

    M = [ uA, C, vA+R*vB,        (R+1)*C ]
        [ uB, C, vC+R*vD-vB,     R*C     ]
        [ uC, C, (R-1)*vD,       (R-1)*C ].            (3)

This derivation applies coordinate by coordinate to any vector of
independent carries. A common physical rail choice is essential: both
equations must certify the same proposed transition realization.

## 2. Rank two forces degenerate rail choices

The second and fourth columns of M are independent: their first two rows
have determinant-C^2. Thus rank M>=2. If two independent coefficient
vectors belong to its kernel, rank M<=2, hence exactly2.

The unique relation annihilating the second and fourth columns is
(1,-2,1). It must therefore annihilate every column, giving

    uA-2uB+uC=0,                                      (4)
    vA-2vC+(R+2)vB-(R+1)vD=0.                         (5)

Boolean ternary words contain no nonconstant three-term arithmetic
progression. To prove this directly, in U-2V+W=0 every ternary residual
digit lies in[-2,2]. The least nonzero residual would have to be divisible
by3, which is impossible. Thus each digit satisfies u+w=2v; for Boolean
digits this forces u=v=w. Equation(4) gives uA=uB=uC.

Rewrite(5) as

    (R+1)(vB-vD)=2vC-vA-vB.

Since every vi lies in[0,H], the right side has absolute value at most
2H=R-1. Therefore vB=vD. Equation(5) then becomes vA+vB=2vC, and the
same ternary argument gives

    vA=vB=vC=vD.                                      (6)

Consequently all read1 realizations are identical and all write1
realizations are identical.

## 3. Every state collapses

Put u=uA=uB=uC and v=vA=vB=vC=vD. Subtract the second row of(3) from
the first. Any coefficient vector in the kernel must satisfy

    gamma*v+delta*C=0.

This is exactly the weight of the shared write1 word. Equation(2) therefore
gives b=c=0. The encoded A state is also0. In multiple carry coordinates,
the same argument applies in every coordinate, so the three state vectors
are identical.

Thus a direct embedding with distinguishable A,B,C cannot have two
independent coefficient directions. Any additional compatible affine
carry equality is proportional to the first after translating offsets;
it cannot provide an independent filter on the same six fixed physical
paths. If a proposed construction uses different refinements or multiple
physical realizations, this theorem applies only when one common set of
six edges with three distinct state vectors satisfies its hypotheses.

## 4. Evidence

The [checker](input_bridge_two_carry_zero_code.py) independently constructs
matrix(3), checks its nonzero minor, the forced row relation and the state
collapse symbolically. It exhausts all read-split triples and append-split
quadruples for every nonzero code word through block length4. The existing
00/12 realization has matrix rank3 and precisely one coefficient direction,
with state values0,14,7, as predicted.

The all-length result is the matrix and digit proof above. Finite enumeration
is supplementary evidence. Author default execution checks the saved
[receipt](input_bridge_two_carry_zero_code.json). Independent full proof,
source, and default-replay review passed.

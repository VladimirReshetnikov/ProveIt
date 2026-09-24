# Ternary local constraints: an exact clause interface and a failed Rule 110 transplant

The odd-prime mask and the conditional base-three Pell kernel provide a
shorter Boolean digit test, but they do not supply a compatible computation
verifier. This note records one local constraint that is carry-free in radix
three and one complete positive counterexample to a direct Rule 110
transplant. It makes no universal operation-count claim.

The finite checker is
`../verification/explore_ternary_local_constraints.py`, with an adjacent
JSON receipt. The general arguments below are separate from its finite tests.

## 1. Exact-one-of-three clauses in two additions

Let q=3^N, N>=1, and J=(q-1)/2. Thus J is the length-N ternary word
whose digits are all one. Suppose A,B,C,D are Boolean ternary words below q.
Then

    A+B=D,
    D+C=J                                             (1)

hold if and only if every digit position of A,B,C contains exactly one one.
The witness D is uniquely A+B.

Indeed, every raw digit of A+B is at most two, so its addition has no ternary
carries. Equality to Boolean D forces a+b=d in {0,1} at each position.
The same no-carry argument applies to D+C. Its equality to J gives d+c=1.
Together these are exactly a+b+c=1. Conversely, under that condition a+b
is zero or one, so the stated D is Boolean and both equations hold.

With A,B,C supplied, compute D=A+B and clause_sum=D+C. These are exactly
two additions, followed by the free equality clause_sum=J. D must also be
included in the Boolean mask; its construction does not establish Booleanity
without that test. If q-1 is already computed, supplying J and checking
2J=q-1 costs one multiplication and one equality. That cost is additional
to the two additions. If q-1 is not available, its subtraction costs another
operation. Packing A,B,C,D and testing their digits remain separate costs.

This is a useful native ternary relation because both raw sides stay strictly
below the radix. It does not establish variable-incidence consistency: the
same logical variable occurring in different clauses must still receive
the same truth value. Without a proved incidence, permutation, or tableau
interface, (1) is just a collection of independent satisfiable clauses.

## 2. Positive fields and the even-word interface

Some valid clause instances have zero A,B,C or D. A compiler allowed to append
fresh fixed true padding clauses can address this without changing the
logical satisfiability question. Append the digit triples

    (1,0,0), (0,1,0), (0,0,1).

Then A,B,C,D are all positive. In a four-field packing

    P=A+qB+q^2C+q^3D,

q is odd, so the parity of P is the parity of the total number of one digits
in all four fields. Each clause contributes 1+(a+b). The three padding
clauses contribute five ones in total. If the resulting word is odd,
append one further fixed clause (0,0,1); it contributes one and makes P even.
The padded word remains Boolean and satisfies 0<P<q^4 for its new length.

This explains a possible source of positive fields and the even-P hypothesis
required by the current half-parameter Pell converse. It is conditional on
the eventual compiler permitting these fresh padding clauses. The note does
not count them as an already implemented input or incidence interface.

## 3. A direct ternary Rule 110 transplant accepts a false endpoint

Changing the current local radix to three would give B=3C and

    14C+4Y=2U+3V,
    2U+3V+alpha=q.                                   (2)

Here 14=2*3^2-3-1 absorbs both spatial shifts, just as 119 does in the
valid radix-eight certificate. Consider the strongest natural surrounding
outer equations

    W=3v, q=v*quot, q-1=H(W-1),
    I+alphaI=v,
    I+WY=C+qF.                                       (3)

The row geometry in this example is a genuine power-of-three rectangle,
and the input guard is I<W/3. Neither condition fixes the local carries.

An exact positive tuple is

    q=W=27, v=9, quot=3, H=1,
    I=C=F=Y=1, B=3, U=3, V=4,
    alpha=9, alphaI=8.

It satisfies every displayed equation. The local sides are both 18.
All four fields U,V,Y,T=B+H=4 are positive Boolean ternary words below q.
Their packing is

    P=U+qV+q^2Y+q^3T=79572<q^4.

The complete P is Boolean and even. Nevertheless the actual Rule 110 update
of B=3 is the ternary word 4, whereas the supplied Y is 1. The moving update
from 3I should therefore end at 12, not the asserted 3F=3. Equivalently, a
nonempty finite moving history cannot have equal positive initial and final
words after a positive height, because its rightmost occupied position moves
one place to the right at every step.

This failure occurs with valid Boolean endpoints, valid power geometry,
positive bounded mask fields, a strong input guard, and the shared field
bound. It is an actual local-carry error, not an input promise violation.

## 4. The false tuple also satisfies the complete mask and positive kernel interface

For the affine ternary mask of
`EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md`, the tuple gives

    L=q^4=531441,
    D0=9L=4782969=3^14,
    r=D0-3P-1=4544252,
    n0=3q^2=2187.

Thus r is even and n0<r<D0=n0^2. The exact factorial-valuation computation
gives v_3(binom(2r,r))=14. The mask is therefore fully satisfied.

The positive converse of `EXPLORATION_BASE_THREE_PELL_KERNEL.md` applies:
q is a power of three, P is bounded and ternary Boolean, and P is even.
It supplies every positive Pell witness of that conditional 43-operation
kernel. This extends the displayed outer tuple to a full positive solution
of the transplanted equations. The counterexample does not rely on a missing
binomial or exponent check.

The checker evaluates sixteen complete scalar clause assignments, 37,448
packed clause triples, 120 positive even-padding cases, all eight displayed
outer residuals, the false update, and the exact three-adic valuation. It does
not materialize the enormous Pell witnesses. Their existence follows from
the general conditional kernel theorem and the explicitly checked hypotheses.

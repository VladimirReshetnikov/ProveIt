# Factor-swapped offset: exact-zero compiler requirements

This is a bounded exploration below the 96-operation frontier.
It is not a new certificate or an impossibility theorem for all
encodings. Fixed numerals are free. The frozen linear-radix proof
and checkers are unchanged.

## Candidate and its target identity

The candidate replaces the positive coefficient by

    Omega=q-e, sigma=(q-e)(q-C^2).

Thus e<q and C^2<q follow from positivity. Retain ell<q and remove
the separate packed upper bound; ell,e<q already imply
ell+e*q<q^2. The proposed packing is

    S=g+q*(ell+e*q+q^2*sigma),
    Tplus=q*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4.

Its third mask tests sigma at q*ell positions, so an indicator at
weight w tests the coefficient at L+w. If the true coordinate
weights are at most M, L>4M, and e is supported in [L-2M,L), then

    [T^(L+w)] sigma
      = [T^(L+w)]e(T)C(T)^2 - [T^w]C(T)^2,
      for w<=2M.

The q^2 term lies above this target, and the -q*e term is absent
because e has no low coefficient at w.

For a desired negative monomial of weight w and a positive monomial
of weight w', its e coefficient would be placed at L+w-w'. Since
this must be below L, every positive monomial must satisfy w'>w.
The negative coefficient is fixed by C^2: minus one for a square
and minus two for a cross product. It cannot independently be
multiplied by a large numeral merely by editing e.

## Why the existing exact-zero compiler does not transfer

Pairing F with -F imposes opposite strict inequalities between
their monomial weights. Even a square-difference copy needs
2v_X>2v_Y in one orientation and 2v_Y>2v_X in the other.

A direct nonnegative quadratic replacement also fails within this
strictly oriented class. Suppose

    F=P-a*M,

where P has nonnegative coefficients, a>0, and every monomial of
P has weight greater than M. Substituting each coordinate by
t raised to its assigned weight makes F negative for all sufficiently
small positive t. Therefore F cannot be an identically nonnegative
quadratic form. This also gives integer counterexamples after a
common denominator is cleared, since the form is homogeneous.

For example, the copy norm X^2+Y^2-2XY would require both
2v_X>v_X+v_Y and 2v_Y>v_X+v_Y. Thus replacing a pair of signs by a
sum of squares does not solve the orientation constraint. This
argument does not exclude systems whose auxiliary equations establish
additional relationships; such a compiler would need a separate proof.

## Two independent indicator obstructions

There is an input-position issue even before approximate zero tests
are considered. The orientation X^2-x^2 has negative weight zero,
so its target would require a unit indicator in ell. The first mask
would then permit a nonzero unit digit of g, and C=x+g would no longer
have actual unit digit x. Reversing the copy equation violates the
weight order. Replacing C by x+B*g repairs that particular issue,
but introduces the multiplication that the candidate was trying to
save.

More generally, an indicator at a product weight w=v_i+v_j also
permits a dummy coordinate D at weight w. Then

    [T^w]C(T)^2

contains 2xD in addition to the desired product term. The old dummy
exclusion argument does not apply: the negative part is this C^2
coefficient itself, rather than a positive-shifted coefficient of
D_code*C^2. A compiler must either use only already allowed variable
positions, separate the variable and target masks, or force all these
new dummy digits to zero. Treating the distinguished negative term
as one monomial before addressing this point is unsound.

## A same-orientation exactness lemma

There is a useful local substitute for opposite signs. Suppose two
zero-carry two-digit tests have raw values 4F and 16F, with
16|F|<B^2 and B a sufficiently large power of two. Then they both
pass the digit mask {0,1,2,3} exactly when F=0.

If F<0, the negative residue has a high digit greater than three.
If F>=0, the low digit of 4F is divisible by four, so it must be
zero. Hence 4F=kB with 0<=k<=3. The second value is 4kB, whose
high digit is 4k, forcing k=0.

This avoids an opposite monomial orientation. However, the candidate's
fixed negative coefficient means that implementing both tests needs
exactly linked scaled coordinates or another way to scale the negative
monomial. Merely multiplying the positive e coefficients changes the
equation. No such exact scaling compiler has been established here.

## Low e digits offer a possible normalization mechanism

The high-band assumption is not mandatory. If e_w=1, then -q*e
contributes a literal -1 at L+w. If the unwanted C^2 coefficient at
w could be forced zero, a positive e coefficient two at
L+w-2v_delta would give the raw target

    2delta^2-1.

With zero incoming carry, this is a particularly strong unit test.
Assume 0<=delta<b=B/H, H>8 and B a sufficiently large power of two.
Its magnitude is less than B^2. Delta=0 gives -1 and fails. Otherwise
the low allowed digit is odd, hence one or three. Low digit three
would imply delta^2=2 modulo B/2, impossible modulo four. Low digit
one gives delta^2=1 modulo B/2. The square roots of one modulo that
power of two, together with delta<B/8, force delta=1. Conversely
delta=1 gives raw value one and passes.

The obstacle is the dummy at w: it contributes -2xD, so the target
is generally 2delta^2-2xD-1, not the displayed unit polynomial.
Trying to zero D by another target introduces another allowed dummy.
The resulting support, carry and termination problem remains open.
The unit lemma is a possible ingredient, not a completed encoding.

## Current status

There is no verified count below 96 from this branch. A successful
continuation needs to solve all three issues together: exactness of
same-oriented arithmetic rows, the queried input's unit position,
and the new dummies at target weights. The lemmas above identify
concrete requirements and two possible local tools; they do not
claim that finite checks establish universal equivalence.

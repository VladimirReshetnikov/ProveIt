# A six-operation two-branch step and its raw-input obstruction

This bounded alternative-model experiment gives an exact positive
six-operation scalar primitive for the shortcut3x+1 map. It also proves
that the natural direct or odd affine raw-input contracts cannot make
the usual odd-coefficient two-branch family strongly universal by
reaching one fixed point. These are separate statements. Neither is a
complete history certificate or a new operation bound for universality.

## 1. The concrete arithmetic primitive

The shortcut map is

    f(n)=n/2                 for even n,
    f(n)=(3n+1)/2            for odd n.

Supply positive A and a native selector beta in{1,2}. The exact step
from positive n to positive m is given by

    n+3=2A+beta,
    m+1=(2A)beta-A.                                           (1)

The first equation uniquely gives A=floor(n/2)+1 and beta=1+(n mod2).
If beta=1, the second gives m=A-1=n/2. If beta=2, it gives
m=3A-1=(3n+1)/2. Conversely these choices satisfy both equations for
every positive n, including n=1. No zero existential quotient is needed.

Compute2A once by A+A. The two input sides cost two further additions.
The output product costs one multiplication, and its two sides cost
two additions/subtractions. Thus the scalar relation costs exactly

    6=1 multiplication+5 additions/subtractions.

If a surrounding digit mask supplies beta in{1,2}, that condition is
already accounted for there. In isolation it can be imposed by
`beta*(3-beta)=2`, costing two more operations. The resulting standalone
step costs8, with all supplied auxiliaries positive. Free equality tests
and fixed numerals have been treated according to the project metric.

This primitive cannot simply be applied to two packed histories by
multiplying their integers. The product then convolves different times:
the coefficient at one time contains cross products from other times.
An exact history compiler would still need coefficientwise selector
alignment, carry control, boundaries and a common finite endpoint. The
six-operation count is deliberately restricted to the scalar step.

## 2. A point target does not fix the direct raw-input contract

Consider the broader positive two-branch family

    f_(a,b)(n)=n/2                for even n,
    f_(a,b)(n)=(a*n+b)/2         for odd n,                    (2)

where a,b are fixed positive odd integers. Accept when a finite iterate
equals a fixed positive target tau. The parameters and target may depend
on the represented program.

With direct initialization n=x, every accepted input n has accepted
ancestors2^k n, because k halving steps reach n. Every nonempty accepted
language is therefore infinite. This direct family cannot represent
arbitrary recursively enumerable languages; even a singleton is excluded.

The common repair n=2x+1 costs two scalar operations, but still has a
sharp obstruction: **a finite accepted language has at most one member**.
This is stronger than merely pointing out that universality has not been
proved for the two-branch family.

## 3. Proof for the odd affine loader

Suppose an odd positive n different from tau reaches tau. Its first
step is the odd branch, with

    y=(a*n+b)/2>0.

Let L be the multiplicative order of2 modulo a, using L=1 when a=1.
For every integer k>=0 define

    n_k=(2^(1+kL)*y-b)/a.                                    (3)

Because2^(kL)=1 mod a, n_k is integral and n_0=n. Its numerator is
odd, and division by the odd a preserves oddness. The sequence is
strictly increasing and unbounded. Its first map step gives

    f_(a,b)(n_k)=2^(kL)*y.

After kL halving steps this is y, which has the original finite suffix
to tau. Hence every n_k reaches tau. For the loader n=2x+1, the numbers
x_k=(n_k-1)/2 are integral and eventually positive; they supply infinitely
many accepted ordinary inputs.

Any accepted set with two different odd starting values has at least
one value different from tau, so the preceding argument applies. The
only possible finite exception is the point tau itself when tau is
odd and belongs to the loader image.

The bound is sharp. Take a=b=3 and tau=5. The initial odd value5 is
accepted immediately. Every other odd value maps first to a multiple
of3, and both branches preserve divisibility by3 thereafter. It can
never reach5. Thus n=2x+1 accepts exactly the positive input x=2.

This theorem is scoped to(2), one point target, and the specified
loaders. It does not cover arbitrary residue-affine programs, rejection
guards, several targets, nonpolynomial encodings, or a more complicated
polynomial loader. It does not turn the open behavior of individual
Collatz trajectories into a decidability theorem.

## 4. Source and evidence boundary

[Stérin and Woods, The Collatz process embeds a base conversion algorithm](https://arxiv.org/abs/2007.06979)
uses precisely the shortcut map in Section1 and constructs a
quasi-cellular representation connecting its binary and ternary
evolution. Its stated result supplies computational structure, not a
strong raw-input universal halting contract for this two-branch map.
The broader generalized-Collatz undecidability theorem of
[Kurtz and Simon](https://doi.org/10.1007/978-3-540-72504-6_49)
does not identify this restricted family with an arbitrary residue map.
The prior detailed contract audit remains
`EXPLORATION_TRANSLATED_COLLATZ_INPUT.md`.

The scalar identities and inverse-family theorem here are original
deductions in this investigation. The checker is
`../verification/explore_two_branch_collatz_primitive.py`, with its
adjacent receipt. It expands the exact six-instruction schedule, checks
2,048 scalar steps, and constructs finite inverse chains from confirmed
target-reaching odd seeds. Cutoff cases are not classified as nonhalting.
The general theorem, rather than finite testing, excludes finite
accepted languages of size at least two under the odd loader.

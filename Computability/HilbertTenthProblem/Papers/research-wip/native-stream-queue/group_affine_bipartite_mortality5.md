# Five-dimensional unrestricted mortality with a two-operation affine input

The universal weighted paired-vector interface admits **five-dimensional
unrestricted mortality** with one affine input matrix loaded in
**2=1M+1A** operations. The varying matrix has rank2. Its singularity is
handled by an exact formula for arbitrary words, not by a restriction on
the number or positions of input letters.

The construction factors the quadratic rank-one reset into two affine
off-diagonal blocks. It improves the dimension of the
[6D affine-loader2 construction](group_affine_cone_mortality6.md), while
the [4D quadratic-loader3 construction](group_weighted_reset_mortality4.md)
remains a separate dimension/input-cost tradeoff. No guard is needed.
Every scalar whose vanishing can make a word mortal already tests both
original paired endpoints simultaneously.

## 1. The inherited scalar, factored differently

Use the fixed signed paired alphabet `(P_i,Q_i)` and ordinary-input
contract of the [projective group theorem](group_projective_zero_mortality6.md).
For fixed program p and x>0,

    alpha=12*2^(p+1), beta=12*2^p,
    t=alpha*x+beta+1, v=(-1,t),

the program accepts x iff a paired word has both first coordinates zero,
equivalently `P_word v=Q_word v=e2`. The first-block matrices belong to
Gamma, whose diagonal entries are1 modulo4.

As in the 4D packet, precompute

    lambda_i=||P_i||_infinity,
    C=diag(-1,1,-1,1),
    D_i=C diag(P_i,lambda_i Q_i) C.

Every D_i is a fixed integral matrix with determinant lambda_i^2>0.
Each original inverse group letter is separately encoded with its own
positive lambda_i; the scaled matrices need not represent a group.
For a fixed-letter word w, write `Lambda=product(lambda_i)`. Its matrix
is `D(w)=C diag(P_word,Lambda Q_word) C`.

Now put the t-weight into the output row instead of the second initial
vector:

    z_t=(1,t,1,t), u_t=(1,0,t,0).

If `a=(P_word v)_1` and `b=(Q_word v)_1`, then

    s(w,t)=u_t D(w) z_t = -(a+t Lambda b).             (1)

The proved strict separation inequality gives `|a|<t Lambda`, and b is
an integer. Thus

    s(w,t)=0 iff a=b=0.                              (2)

This uses the fixed subgroup hypothesis; it does not hold for arbitrary
SL2 pairs. The sharp inequality and the order4 rotation counterexample
are proved in the 4D packet. No word-dependent norm or Lambda is supplied
as an untyped arithmetic witness.

For reference, the quadratic rank-one matrix `z_t u_t` has the same
mortality predicate as the committed4D reset: with
`S_t=diag(1,1,t,t)`, one has

    S_t (z_t u_t)=R_t S_t,

where R_t is that packet's varying reset. S_t commutes with every fixed
D_i and is invertible over Q for t>0. This conjugacy is a proof identity,
not an uncharged input conversion in the affine source below.

## 2. A general alternating-block linearization lemma

Let z be any nonzero d-column and u any nonzero d-row over Q. Let the
fixed d-dimensional letters D_i be invertible. Define

    T=[0_(d by d), z; u,0],
    E_i=diag(D_i,1).                                 (3)

For fixed products `M_j=diag(D_j,1)`, put `s_j=u D_j z` and consider
the core with k occurrences of T, in algebraic product order,

    A_k=T M_(k-1) T ... M_1 T.

Products over an empty index set mean1. Direct block multiplication
gives, for k=2n>=2,

    A_(2n)=diag(
        (product s_j over even j=2,...,2n-2) z u,
        product s_j over odd j=1,...,2n-1).           (4)

For k=2n+1>=1 it gives

    A_(2n+1)=[0,
              (product s_j over odd j=1,...,2n-1) z;
              (product s_j over even j=2,...,2n) u,0]. (5)

The base case is (3). Left multiplication by `T M_k` alternates (4)
and (5), appending s_k to the indicated parity. In particular

    T M_1 T=diag(z u,s_1),
    T M_2 T M_1 T=[0,s_1 z;s_2 u,0].                (6)

The upper block in the first identity is z u, independent of D_1.
These identities also fix the chronology unambiguously.

Since z, u and z u are nonzero, a core is zero exactly when the product
of its odd-indexed bridge scalars and the product of its even-indexed
bridge scalars are both zero. In particular a zero core requires some
s_j=0. Arbitrary exterior words in the E_i are invertible and cannot
change whether the core is zero. Words with no T are invertible; those
with one or two occurrences cannot be zero, even if their one available
bridge scalar vanishes.

Conversely, if one fixed word M=diag(D,1) has scalar `s=u D z=0`, then

    T M T M T=s T=0.                                (7)

Therefore the alphabet in (3) is mortal iff one fixed-word scalar u D z
vanishes. Equivalently, it is mortal iff the original fixed letters D_i
and rank-one reset z u are mortal. The latter equivalence also follows
from the usual rank-one factorization, but (4)-(7) directly handle the
singular varying letter T.

The fact that two channels can be killed by different bridge words
causes no error here: **each individual zero bridge is already a full
scalar witness** to the original problem. This is precisely what was
missing from the old independent two-block reset.

## 3. The five-dimensional universal alphabet

Apply (3) with d=4 and the vectors and fixed letters of Section1. The
single varying matrix is

    T(t)=[0,0,0,0,1;
          0,0,0,0,t;
          0,0,0,0,1;
          0,0,0,0,t;
          1,0,t,0,0],

and the fixed matrices are `E_i=diag(D_i,1)`. T(t) is integral,
nonnegative, affine in t and has rank2. Its rows and columns supported
on the off-diagonal blocks exhibit rank at most2; the minor on rows
and columns `(1,5)` has determinant-1, giving rank at least2. It is
singular, whereas each fixed E_i has determinant lambda_i^2>0.

There is no hidden nilpotent input-only word. Indeed

    u_t z_t=1+t>0,
    T(t)^3=(1+t)T(t),                               (8)

so all positive powers of T(t) are nonzero. Empty bridge segments in
(4)-(5) contribute1+t. The full arbitrary-word proof remains necessary;
checking (8) alone would not suffice.

By (1), (2) and the general lemma, with one fixed alphabet of size s,

    x is accepted by program p
      iff {E_1,...,E_s,T(alpha*x+beta+1)}
          generates the zero matrix.                (9)

A common paired endpoint word supplies a mortal word using exactly
three occurrences of T by (7). Any mortal word, regardless of its number
or order of input letters, contains a fixed-letter bridge that supplies
such an endpoint by (4)-(5). No free regular-language constraint is
imposed. The alphabet consists of s fixed5-by-5 integer matrices and one
varying matrix; the inherited numerical universal alphabet is still
abstract rather than transcribed into this packet.

## 4. Paid input and uniform-certificate scope

The entire25-entry matrix has the literal input source

    scaled=alpha*x, t=scaled+(beta+1).

This costs exactly **2=1M+1A**, with zero existential witnesses or
comparisons. Every varying entry is a copy of t; the other entries are0
or1. Computing beta+1, lambda_i and the fixed matrices is compilation
of fixed program data. Fixed signed integer numerals are allowed for
the E_i. There are no runtime t-squared entries, input-dependent
negations or uncharged multiplications by fixed constants in the loader.

The result improves6D affine-loader2 to5D affine-loader2 while retaining
unrestricted mortality. It supplies no global minimal-dimension theorem,
and it does not contradict lower bounds for earlier exact scalar series:
both the scalar model and the singular-input architecture have changed.

The unbounded existence predicate in (9) is exactly the existing paired
endpoint. Its paid four-history certificate can therefore be imported
without new arithmetic witnesses for the two channels, their parity
products or a word in the5D matrices. For a stable named example, the
[shared-history/strong-unit compiler](group_projective_strong_unit_product.md)
gives its279-operation, degree3502 illustration with42 positive
witnesses under the same fixed-table and padded-program hypotheses.
Later equivalent compiler refinements compose independently.

This is an existence reduction, not a cheaper complete gate count merely
because the matrices are smaller. A certificate for an independently
supplied arbitrary5D word, its duration, or all its input-letter
positions still needs a paid selected-history encoding. The numerical
universal75/88 bounds are unchanged.

## 5. Exact checks

The [source](group_affine_bipartite_mortality5.py) and
[receipt](group_affine_bipartite_mortality5.json) check48 ordinary-input
loaders, every entry of T, all3-by-3 minors, a nonzero2-by-2 minor and768
nonzero input powers. They also check the conjugacy to the4D reset.

The general parity formula is tested on1,024 exact products with
physical dimensions2,3,4,5, arbitrary invertible exterior words and up
to ten input occurrences. These include forced zero bridges on both
parities, so the test does not rely only on nonzero cases. Another1,024
weighted paired-word scalars verify (1), (2) and the three-input identity
(7), with128 additional actual-alphabet channel products.

Sixteen actual finite one-relator accepting words yield three-input
zero matrices and remain zero with nonempty exterior words. Their
wrong-input mutations are nonzero. Even their accepting bridge cannot
make a two-input product zero. Thirty-two pairs of the old independent
one-block bridges still produce nonzero alternating products.

These finite alphabets illustrate the parametric theorem, not a numerical
enumeration of the universal alphabet. Run the checker normally to
compare its deterministic receipt, or with `--write-receipt` to regenerate
it. Universality rests on the inherited projective theorem and the full
arbitrary-word equivalence (9).

Independent and root full proof/source reviews and fresh default receipt
replays passed. A separate rational-matrix implementation checked288
channel and exterior cases in physical dimensions1 through6 with up to
12 input occurrences, including69 zero cases and generic u*z=0 boundary
cases. This supplements the general parity proof rather than replacing it.

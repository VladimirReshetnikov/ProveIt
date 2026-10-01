# Four-dimensional mortality with two resets, and the failure of unrestricted resets

The established universal paired-vector predicate has a four-dimensional
matrix adapter with a **two-operation affine input matrix**. Its exact
contract requires a product containing at most two copies of the input
reset. Equivalently, one may restrict products to the fixed regular form
`R_x F* R_x`, where F is the fixed invertible alphabet.

Dropping this restriction destroys the predicate: a three-reset zero
product exists for **every** positive input, independently of all group
relators. The two blocks can be erased by different intervening words.
Thus the minimum possible number of resets is exactly two on members
and three on nonmembers. This gives both a smaller controlled interface
and an explicit obstruction to replacing the synchronized six-dimensional
rank-one construction by the direct sum of two rank-one resets.

The arbitrary selected word and its regular-language control are not
encoded into arithmetic here. The two-operation figure is only the input
loader; it is not a complete universal Diophantine bound. The
[source](group_two_reset_mortality4.py) and
[receipt](group_two_reset_mortality4.json) audit the exact matrix identities
and finite word witnesses.

## 1. The inherited universal input

Use the exact theorem in Sections 1–3 of
[group_projective_zero_mortality6](group_projective_zero_mortality6.md).
It supplies a fixed finitely generated subgroup K_U of Γ×Γ and a fixed
finite signed generator alphabet for it. Here

    a ↦ A=[1,1;0,1], b ↦ B=[1,0;12,1],
    Γ=<A,B,V A V^(-1),V² A V^(-2)>, V=[1,0;4,1].

The fixed group represents all r.e. sets S_p of positive integers through

    U={2^p(2x+1):x∈S_p},
    y=2^p(2x+1), r=12y,
    L=B^(-y) A B^y=[1+r,1;−r²,1−r],
    t=r+1, v=(-1,t)^T.

Its exact endpoint theorem is

    x∈S_p iff ∃(P,Q)∈K_U: (Pv)_1=(Qv)_1=0
           iff ∃(P,Q)∈K_U: Pv=Qv=e2.             (1)

This is a theorem about the specified Γ and K_U. The proof uses Γ's
congruences, its precise lower-triangular stabilizer, and an injective
pullback to the original graph group. It does not follow from a claim of
undecidability alone or from arbitrary determinant-one matrices.

Concretely K_U is the faithful matrix image of

    M_a=(a,1) M(H) (a^(-1),1),
    M(H)={(g,h):π(g)=π(h)},

for the fixed finite presentation H from the parent. In particular it
contains all pairs

    (a w a^(-1),w), w∈F_4.                       (2)

Only (1) and the explicit diagonal subgroup (2) are needed below. The
finite presentation and its numerical universal matrix generators remain
inherited abstractly; the toy presentations in the checker do not
instantiate that universal alphabet. No new external universality result
is invoked in this packet.

## 2. Exactly what repeated block resets test

Let F be any alphabet of integral invertible block-diagonal matrices with
s blocks. In block i fix a nonzero column v_i and a nonzero row u_i, and put

    R=diag(v_1 u_1,...,v_s u_s).

Consider a word with k reset occurrences,

    W=A_0 R A_1 R ... R A_k,  A_j∈F*.

For k≥1, its i-th block is exactly

    W_i=(A_0^(i) v_i)
        [ product from j=1 to k−1 of (u_i A_j^(i) v_i) ]
        (u_i A_k^(i)).                            (3)

This follows by multiplying each adjacent rank-one pair. Both outside
vectors are nonzero because the A_j blocks are invertible. Their outer
product is nonzero over the integers. Hence

    W=0 iff for every i there is an internal j
            with u_i A_j^(i) v_i=0.               (4)

The same internal j need not work for different blocks. In particular:

* No zero product uses zero or one reset.
* A zero product with at most two resets exists exactly when a single
  A∈F* makes all s scalar coefficients zero simultaneously.
* Unrestricted mortality holds exactly when each block has some scalar
  zero word, with different words allowed for different blocks.
* If unrestricted mortality holds, s+1 resets suffice: choose a zero
  word A_i for each block and multiply `R A_1 R ... A_s R`.

The last two assertions have both directions. A zero product supplies the
necessary individual words by (4), and the displayed product is zero by
that same formula. Empty internal words and arbitrary invertible outside
words are included. For two blocks, three resets can therefore suffice
even when no two-reset zero exists.

This is an exact exchange from “one word works for every block” to “each
block has a word.” It is scoped to this block-diagonal reset construction;
it is not a lower bound on all four-dimensional mortality adapters.

## 3. A nonnegative idempotent reset with affine input

Let C=diag(−1,1), so C²=I. Conjugate the fixed alphabet of K_U once to
obtain the fixed alphabet F consisting of

    diag(C P C, C Q C)

for its signed generators (P,Q). These are invertible integral 4×4
matrices. Their signs are fixed program data; positivity is not claimed
for their entries.

For the ordinary input x, define

    w=(1,t)^T, E_t=w e1^T=[1,0;t,0],
    R_x=diag(E_t,E_t).                            (5)

This reset is integral, nonnegative, rank two, and idempotent:
`R_x²=R_x`. All its nonzero entries are positive. It relates to the
original signed rank-one reset by

    E_t=−C(v e1^T)C,
    e1^T(C P C)w=−(Pv)_1.                       (6)

Thus, by (1), (3), and (6),

    x∈S_p iff ∃A∈F*: R_x A R_x=0
           iff some product over F∪{R_x} is zero
               and contains at most two copies of R_x.           (7)

The latter implication does not need the outside words to be absent:
they can be removed by their inverses or by (3). Products with fewer
than two resets are nonzero. Since R_x²=R_x, an empty middle word is
also nonzero. Both formulations therefore require a nontrivial middle
witness whenever they accept.

There is one fixed invertible alphabet F for all programs. The full
mortality alphabet has the single **input-dependent** additional matrix
R_x. Calling every matrix in F∪{R_x} fixed would be incorrect.

For a fixed program p, precompute the positive numerals

    α=12·2^(p+1), β=12·2^p, γ=β+1.

The entire input matrix (5) is loaded by the literal source

    scaled=α*x,
    t=scaled+γ.

This costs **2=1M+1A**, degree one, and introduces no existential
coordinates or equations. The matrix entries are copies of t and fixed
zeros and ones; copies cost no arithmetic. Computing γ from p is fixed
program construction, not an uncharged input operation. Arbitrary
positive α,β define the same arithmetic loader, but the universal
corollary uses exactly the compatible program constants and K_U above.

## 4. A three-reset zero on every input

The failure of unrestricted mortality does not require searching for
subgroup words. For the target L above, set

    G_1=(L,A^(-1) L A),
    G_2=(A L A^(-1),L).

Both are in K_U by (2): use w=a^(-1) a_y a for G_1 and w=a_y for G_2.
These are finite words in the fixed diagonal generators and their
inverses, for every positive y. Their lengths depend on y; this
construction does not treat those words as a free arithmetic encoding.

Direct multiplication gives the exact two scalar pairs

    ((G_1^(1)v)_1,(G_1^(2)v)_1)
        =(0, r(r²+2r+2)),
    ((G_2^(1)v)_1,(G_2^(2)v)_1)
        =(r(r²−2),0).                             (8)

Since r=12y≥12, each displayed nonzero value is strictly positive.
Consequently neither intervening word has simultaneous zeros. Let
G'_j denote its fixed C-conjugated 4×4 image. Nevertheless,

    R_x G'_1 R_x G'_2 R_x=0                      (9)

by (3): its first block has the first scalar factor zero and its second
block has the second factor zero. The signs in (6) do not change this.
Each shorter product `R_x G'_j R_x` is nonzero.

Equations (7) and (9) prove the sharp dichotomy for this family:

    minimum number of reset occurrences in a zero product
      = 2 if x∈S_p,
      = 3 if x∉S_p.                              (10)

For a concrete rejected fixture take S empty and choose the identity
finite presentation H=G_S, the free group on a,b. Its conjugated fibre
subgroup is then the conjugated diagonal subgroup.
The projective theorem rules out every two-reset zero at positive y,
while (9) still gives a three-reset zero. The checker also verifies
bounded words in this empty-relator presentation directly. Finite
enumeration supplements the general argument; it does not establish
nonexistence of all words by a search cutoff.

## 5. Paid and unpaid interfaces

The six-dimensional parent uses one rank-one reset after summing two
squares. Its repeated-reset scalar factorization preserves a common
zero word, and therefore supports unrestricted mortality. The present
four-dimensional reset has rank two. It saves one loader multiplication
and two dimensions for **controlled** mortality, while unrestricted
mortality becomes the all-input predicate.

The regular language `R_x F* R_x` can be described by a three-state
partial automaton: one reset from the initial state to the middle state,
all fixed invertible letters looping at the middle state, and one reset
to the final state. Missing transitions reject. This is a combinatorial
description, not a paid Diophantine controller. If physical shear codes
replace fixed matrix letters, the complete macro-language control is
also required; arbitrary shear words would invalidate (1).

Likewise the product A in (7) can have unbounded length. This packet
supplies no uniform positive-integer certificate for its selection,
iteration, or macro boundaries. The existing paired-vector compiler
already encodes the simultaneous endpoint of (1). Applying that compiler
would retain its paid selection, history, and control costs; the reset
notation does not eliminate them. No complete operation-count improvement
is asserted here.

The constructive result is an exact affine-input, four-dimensional
controlled-mortality representation with a fixed alphabet. The obstruction
is stronger than an isolated counterexample: the naive unrestricted
replacement always loses all input information, and the explicit
three-reset witness does so without using any presentation relator.

## 6. Reproducible checks and their limits

Run from this directory:

    python group_two_reset_mortality4.py

`--write-receipt` regenerates the stored receipt. The checker uses exact
integers and independently forms dense matrix products. Its tests cover:

* 1,536 block-factorization cases with one through four blocks, zero
  through six resets, arbitrary signed nonzero boundary vectors, and
  deliberately inserted single-block zero factors;
* 512 ordinary-input loader and explicit three-reset examples, checking
  the fixed diagonal word witnesses, both formulas in (8), idempotence,
  nonnegativity, and failure of both shorter products;
* all reduced free words of length at most six on two generators at four
  positive targets in the empty-relator fixture;
* 24 actual accepting finite one-relator fibre-product words, plus a
  wrong-input rejection for each word and comparison with the six-
  dimensional synchronized scalar.

The general proof establishes (3)–(10) for arbitrary word lengths. These
checks do not instantiate the universal finite presentation, decide a
universal subgroup, or pay for arbitrary word selection.

An independent proof/source/default review found no issue with the
factorization, reset-count quantifiers, fixed diagonal word witnesses,
sign change or loader. An additional 384 direct dense-matrix cases at
integer r between 1 and 999 checked both scalar pairs, the three-reset
zero, and nonvanishing of the two shorter bridges.

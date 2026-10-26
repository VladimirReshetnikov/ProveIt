# Sparse constructor coding preserves finite refutations

## Status

This is a new ordinary proof for the proposed sparse coding, not a formal
Lean/Rocq certificate. It supplies the semantic interface needed to replace
the literal source constructor polynomials. It does not by itself authenticate
an entire compiled Diophantine equation or establish improved final metrics.

The reference calculus is the numerical C222 calculus in the pinned
`KCode222.lean`, whose rules are truth at 0, modus ponens, generalization,
eight unguarded constructor-term axiom schemata, and the bundle schema with
the two guards `c != a` and `c != b`. Its false code is 1. The retained
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` supply the final
logical calibration.

## 1. The sparse arithmetic constructors

For nonnegative integers x,y put

    q(x,y)=(x+y)^2+x,
    I_s(x,y)=4q(x,y),  M_s(x,y)=4q(x,y)+1,
    A_s(x,y)=4q(x,y)+2,  E_s(x,y)=4q(x,y)+3.

The unchanged C222 schemata are evaluated using these four constructors.
In particular no assertion that every natural number encodes a formula is
made or required. The codes 12,13,14,15 are the first unused constructor
values: their quotient by four is 3, which is outside the range of q.

For fixed s=x+y the values of q are exactly the integer interval
[s^2,s^2+s]. These intervals are disjoint. Thus q is injective, and its
partial inverse at an integer r is obtained by setting s=floor(sqrt(r)),
x=r-s^2, y=s-x, accepting precisely when x<=s. Consequently the four
constructors are injective and have mutually disjoint ranges (by residues
modulo four). They satisfy

    I_s(0,0)=0,  M_s(0,0)=1,

and each nonzero constructor output is strictly greater than both inputs.
Indeed if x+y>=1 then 4(x+y)^2>=4(x+y)>max(x,y); if both inputs vanish,
the nonzero outputs are 1,2,3.

The reference Cantor constructors I_o,M_o,A_o,E_o have exactly the same
injectivity, range-disjointness and strict-descent properties, except that
their union covers all natural numbers. The ordinary quotient formula is

    I_o(x,y)=2(x+y)(x+y+1)+4y,

with offsets 1,2,3 for M_o,A_o,E_o. Their only zero constructor output is
I_o(0,0). These are algebraic facts about the explicit coding, independently
of any consistency assumption.

## 2. Canonical finite trees

Decode a sparse numeral recursively. Zero is the leaf 0. A positive
numeral in a constructor range is the corresponding constructor node,
with its two recursively decoded arguments. A positive numeral outside
all four ranges is an extra atomic leaf named by that numeral. The recursion
terminates by strict descent. Constructor injectivity and disjointness
make this tree unique.

The convention that 0 is a leaf identifies the single syntactic
configuration I(0,0) with 0. Apart from this normalization there are no
identifications. A normalized tree has no I node whose two children are
both 0. Define its height in the usual way: leaves have height zero and
a constructor node has height one plus the maximum of its child heights.

The same decoding for a Cantor numeral has no extra atomic leaves.

## 3. The finite-marker lemma

**Lemma.** Let S be any finite collection of normalized sparse trees, and
include all their subtrees in S. There is an assignment of a Cantor numeral
to each extra atomic leaf appearing in S such that substitution followed
by Cantor constructor evaluation is injective on S, fixes 0 and 1, and
commutes with every constructor occurrence in S.

**Proof.** Let D be the maximum height of the trees in S and let k be the
number of distinct extra atomic leaves. If k=0 the identity on normalized
tree structure suffices. Otherwise enumerate the extra leaves as
j=0,...,k-1 and set L=max(D,k). In the Cantor coding form the chain

    W_0=0,  W_(r+1)=A_o(0,W_r).

The normalized tree for W_r has height r. Choose markers

    m_j=I_o(W_L,W_j),  0<=j<k.

All markers have the same height L+1, and they are pairwise distinct by
constructor injectivity. Substitute m_j for the j-th extra leaf.

A tree without extra leaves retains its original normalized tree height,
which is at most D<L+1. A tree with extra leaves has substituted height

    L+1+max{depth of an extra leaf in that tree}.

The constant-only branches have height at most D and cannot dominate the
displayed height. Hence a single extra leaf, of substituted height L+1,
cannot coincide with the image of a constructor tree: a constructor tree
with extra leaves has greater height, and a constructor tree with none
has smaller height. It also cannot coincide with 0. Two distinct extra
leaves have distinct markers. If two remaining nonzero constructor trees
have equal substituted values, disjointness of the four Cantor constructor
ranges identifies their root symbols, and injectivity identifies both
children. Repeating this argument terminates at the already-separated
leaves. Thus their original trees were equal. Normalization at I(0,0)
causes no additional collision because it is imposed in both codings.

Substitution is a constructor homomorphism wherever the relevant trees
occur. It fixes 0 by definition and fixes 1=M(0,0). This proves the lemma.

The assignment deliberately depends on the finite set S. There is no
global injective constructor homomorphism from the sparse coding to the
Cantor coding fixing 0: the constructor closure of 0 already exhausts the
Cantor naturals. A claim of a global bijection would therefore be false.

## 4. Refutation transfer in both directions

**Theorem.** The sparse C222 calculus derives 1 if and only if the original
Cantor C222 calculus derives 1. The two transformations of finite proofs
are effective and formalizable in ZFC.

**Proof, sparse to Cantor.** Start with a finite sparse derivation. Take
all numerals used as rule parameters, premises and conclusions, together
with every intermediate constructor-term value in each instantiated rule.
Decode them and add all subtrees to obtain a finite set S. Apply the
finite-marker lemma. Every equality obtained by evaluating a constructor
term in an axiom or inference is preserved by the homomorphism property.
The premise/conclusion equalities used in modus ponens are preserved for
the same reason. Truth and generalization transfer directly. For a bundle
instance, the original finite set includes the three parameter trees
a,b,c; injectivity on S preserves c!=a and c!=b. Thus every transformed
line is a legitimate Cantor C222 inference, and the last line remains
1. This is a finite proof transformation, not a model-existence argument.

**Proof, Cantor to sparse.** Every Cantor numeral has a finite normalized
tree using only the leaf 0. Evaluate that tree with the sparse constructors.
The uniqueness of normalized sparse decoding proves that this map is
injective on all Cantor numerals. It commutes with constructors, including
I(0,0)=0, and fixes 0 and 1. Transport all proof lines, parameters and
guards under this global injection.

All constructions use finite recursion, integer square roots, finite
lists, and evaluation of explicit integer polynomials. Their termination
and the inductions above are formalizable in ZFC. No soundness,
consistency or actual existence of a refutation is assumed.

**Corollary.** Composing the theorem with the named original C222/ZF/ZFC
calibrations gives, provably in ZFC,

    a finite sparse-C222 derivation of 1 exists
        iff a finite syntactic ZFC refutation exists.

The auxiliary d used by the arithmetic source to certify a bundle guard
is not transported through the marker map. After translating a,b,c,
rechoose d=abs((c-a)(c-b))-1. This is a nonnegative integer and satisfies
((c-a)(c-b))^2=(d+1)^2. In unrelated rule branches d is an ordinary schema
parameter and is transported in the usual way. These roles belong to
alternative local branches and do not need the same choice simultaneously.

## 5. A compatible global label bound

If 0<=u,v<=M then every sparse constructor C satisfies

    C(u,v)+1 <= E_s(M,M)+1
              =16M^2+4M+4 <=16(M+1)^2.

If every leaf is below t, a constructor tree of depth r has value plus one
at most 16^(2^r-1)*t^(2^r). The source schemata have the same constructor
trees as the pinned square-shell implementation, so the authenticated
maximum depth 19 is unchanged. With d=2^19 the usable bound is

    L=16^(d-1)*t^d.

Thus the old factor-eight depth bound must not be silently reused.

For the standalone growth interface, retain t=16+4z^2 and replace the
Pell center 4t+1 by 8t+1. Introduce the same three coordinates X,Z,u and
impose the quadratic rows

    Z=tF,
    X^2-64Z^2-16ZF=1,
    F=2^19*t*(2u+1).

These imply a positive Pell index n with abs(F)=Y_n(8t+1). The recurrence
gives Y_n(8t+1)=n modulo 8t and, since the center is odd,
v_2(Y_n)=v_2(n). Hence 8t divides n and v_2(n)=19+v_2(t), which imply
n>=d*t. Standard recurrence growth gives

    abs(F)>=(16t+1)^(n-1)>=(16t)^(d*t-1)>=L^t,

the last ratio being 16^(t-1)/t>=1. No sign of F is used here.

The completeness argument of the pinned standalone-growth proof applies
with 8t+1 throughout. Its inputs require only an odd center congruent to
1 modulo four, Y_n(a)=n modulo t, the exact two-adic valuation identity,
the Pell composition identities, and the permutation property of Y_s(a)
modulo powers of two when a=1 modulo four. All hold unchanged. Specifically,
choose t=16 modulo 2^26, n_0=d*t, y_0=Y_(n_0)(8t+1), and
a_0=X_(n_0)(8t+1). Then y_0/(d*t) is odd, v_2(y_0)=23, and a_0=1 modulo
four. Choose a positive odd s in the prescribed residue class so that
F=y_0 Y_s(a_0)=2^23 modulo 2^N with 2^N>t. This makes the supports of F
and t disjoint and the selector binomial(F+t,t) odd, with arbitrarily
large admissible F. Every subsequent beta, CRT, radix and signed bootstrap
step uses this bound and parity data, not the old exact constructor code.

## 6. Scope of the proposed improvement

This removes all special complementary-shell arithmetic from A and E:
the four constructors become constant offsets of one common quadratic.
It is a change of syntax coding, with a finite-refutation equivalence proof,
not a polynomial identity between the old and new systems. Final variable,
operation, monomial and coefficient counts require a fresh compiler run,
updated label-bound data, new projection certificates and exact expansion.
The new leading coefficient doubles from the old shell constructors;
coefficient height can therefore increase even if a circuit shrinks.

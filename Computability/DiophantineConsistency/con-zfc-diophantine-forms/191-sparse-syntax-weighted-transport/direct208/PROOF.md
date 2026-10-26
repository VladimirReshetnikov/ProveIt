# Proof of the 208-variable sparse-code construction

## 1. Exact theorem and definition

For each row of `equations/principal208/equation.json`, interpret its list
of pairs `[coefficient,[variable indices]]` as the sum of coefficient times
the indicated monomial. Empty index lists are constants; repeated indices
give ordinary fixed powers. Let R_0,...,R_147 be these quadratic polynomials.
The equation is P_208=sum R_j^2=0 on all of Z^208. Over the integers this is
equivalent to all 148 rows being zero. The adjacent expansion prints every
collected coefficient of the same single polynomial.

The new arguments below, composed with the named inherited C222/ZF/ZFC
calibrations, give the ordinary mathematical theorem formalizable in ZFC:

    (exists x in Z^208, P_208(x)=0)
        iff (a finite syntactic ZFC refutation exists).

Negating both sides gives nonsolvability iff Con(ZFC). The construction
does not assume consistency, and does not establish that either side of
this equivalence holds.

## 2. Replacing surjective coding by a sparse coding

The new constructors are I=4((a+b)^2+a), M=I+1, A=I+2 and E=I+3.
The intervals [s^2,s^2+s] for s=a+b are disjoint. Thus the underlying
pairing is injective, and the four tags give disjoint constructor ranges.
Every nonzero constructor result exceeds both arguments. The identities
I(0,0)=0 and M(0,0)=1 agree with the original Cantor coding.

Some natural numbers now lie outside all constructor ranges. A sparse
number decodes to a finite normalized tree with these numbers as extra
atomic leaves. They cannot be ignored in soundness, because an arbitrary
Diophantine zero may use them as parameters. The proof in
`proofs/SPARSE_RECODING_PROOF.md` addresses precisely this issue.

For a finite derivation, close all its parameter and intermediate trees
under subtrees. If their maximum height is D and they use k extra atoms,
set L=max(D,k), form W_0=0, W_(r+1)=A_old(0,W_r), and replace atom j by
I_old(W_L,W_j), 0<=j<k. The markers are distinct trees of height L+1.
An original tree with no extra atom has height <=D. A constructor tree
with extra atoms has substituted height strictly larger than L+1.
Disjoint root tags and induction on children then prove injectivity on
the whole finite collection. All constructor evaluations and the two
freshness disequalities are preserved. Truth 0 and falsity 1 stay fixed.
This translates every sparse refutation into an original C222 refutation.

Conversely, decode every original Cantor number into its finite tree over
0 and evaluate that tree with the sparse constructors. This global
injection fixes 0 and 1 and preserves all rules and disequalities. Hence
the two calculi have a finite refutation simultaneously. There is no
claim of a global inverse injection into the saturated old term algebra;
the finite marker construction is the required weaker statement.

## 3. The exact replacement of the local arithmetic

The arithmetic parent `source/parent216.json` encodes a sequence of
backward proof steps using weights w(j)=1+Fj, beta states S,S', and local
natural parameters a,b,c,d. Its first four rows and every row after the
old syntax block remain intact, apart from the growth and horizon edits
described below. Old rows 4 through 80 are replaced by 75 new acyclic
quadratic definitions. Their only outputs crossing into retained rows
are:

* coordinate 79, the sum of the squares of the guarded-bundle difference
  and its freshness defect;
* coordinate 95, the square of the product of all eleven other branch
  differences: truth, eight ordinary axioms, MP and generalization.

The freshness defect is ((c-a)(c-b))^2-(d+1)^2. Because the decoded d is
nonnegative, a zero of this defect is equivalent to c!=a,b with an
appropriate d. The signed orientation of any single unguarded factor is
irrelevant after squaring the full product. With the two beta remainder
squares, the retained local expression vanishes exactly when both beta
equations hold and one permitted rule branch applies.

Each new definition has a new output with coefficient one, occurring
linearly, and depends only on earlier outputs and the preserved external
inputs. Therefore it has exactly one integer completion for every input.
The checker independently reconstructs all nine full constructor trees,
the guarded branch, MP, generalization and the eleven-factor product by
linear elimination of exact quadratic identities. It uses no function
from the compiler. It also checks the complete cut and retained row list.

The old private FS coordinate has one remaining definition FS=F*S after
the cut; this is a harmless definitional extension. Its sole row has a
unit coefficient, and a later certified projection removes it. No old
syntax output other than coordinates 79 and 95 crosses the cut.

## 4. Bounds and the compatible growth certificate

For arguments at most M, each sparse constructor satisfies

    C(a,b)+1 <=16M^2+4M+4 <=16(M+1)^2.

The schema trees retain maximum depth 19. Put d=2^19. If t>=2 and all
local parameters are below t, every label is below

    L=16^(d-1)*t^d.

The old factor-eight bound is not used for this new coding. Change the
standalone Pell growth block to exactly

    Z=tF,
    X^2-64Z^2-16ZF=1,
    F=d*t*(2u+1).                                     (G)

After t is oriented, this is the Pell equation with center 8t+1. If
|F|=Y_n(8t+1), its congruence Y_n=n modulo 8t and its valuation identity
v2(Y_n)=v2(n) imply n>=dt. Thus

    |F| >= (16t+1)^(dt-1) >= (16t)^(dt-1) >= L^t,

because the last ratio is 16^(t-1)/t>=1. Once the retained front bootstrap
orients F, this is exactly the label product-separation hypothesis.

The independent local bound in `proofs/SPARSE_LOCAL_BOUND_REVIEW.md`
also checks the CRT congruence-to-equality step. With
R=2+t+x+y+F, the eleven-axis product squared is below R^1092, the
guarded joint factor is below R^2097157, and the two beta squares give
the conservative strict bound

    Local < R^2098250 < R^(2^23).

The retained endpoint relations give R<2x and x>2^32. Therefore
Local<2^x. The inherited bound and divisibility of the CRT modulus force
the decoded local congruence to be an actual zero. This is an unbounded
polynomial-degree argument, not a numerical test of sample inputs.

## 5. An affine signed horizon with minimum two

Replace the parent's t=16+4z^2 by t=2+4z. Initially |t|>=2. The final
equation of (G) gives F nonzero and even with |F|>=2^19|t|>=2^20.
The main square frame includes F^2, so its required lower threshold
already holds. The inherited C-anchor argument, valid with signed frame
atoms, authenticates the signed principal Pell pairs before front signs.

Since C is even, D=2(C+F+1) is nonzero and |D|>=2. The retained q=D^x
request forces x>=0. The beta equations include y=F(2v+1) and
x=1+[1+(t+1)y]r_t. If x=0 the last product would be -1, whereas

    |1+(t+1)y| >= |y|-1 >=|F|-1 >1.

Thus x>=1 and |q|>=2. The existing q^t request now forces t>=0, hence
t>=2. Only after this step is the standalone Pell classification in
Section 4 used. It supplies |F|>t; the retained q^(y+1) and (q+1)^(F+t)
requests and beta endpoints then recover F>0, y>=F, C>0 and
x>=2+(t+1)y. The proof is noncircular.

At t>=2 the stronger new label bound gives F>=t^(2t)>=(t!)^2, enough
for every generalized binomial-CRT radius. It also gives
F>=2^(10d-8)>2^32. The inequalities used in Section 4 follow from
F>=t^2, y>=F and x>=2+(t+1)y. The affine radix remains larger than 2C;
all normalized binomial low-tail bounds remain valid. A fuller threshold
audit is in `proofs/AFFINE_GROWTH_HORIZONS.md`, with the factor-eight
growth estimate replaced here by the explicitly stronger factor-sixteen
estimate.

For completeness, choose a positive cofinal horizon t=2 modulo 2^23,
larger than the finite proof and all its local parameters. Then v2(t)=1
and bit 20 of t is zero. Let n0=dt, y0=Y_(n0)(8t+1), a0=X_(n0)(8t+1).
The standard congruence and valuation identities give y0/(dt) odd,
v2(y0)=20, and a0=1 modulo four. The retained Pell residue permutation
modulo powers of two supplies arbitrarily large odd s such that
F=y0Y_s(a0)=2^20 modulo 2^N, with 2^N>t. The binary supports of F and
t are disjoint, so B=binom(F+t,t) is odd. Choose the beta odd multiplier
to include every odd prime <=t and exceed all finite state values. Then
choose x, the CRT representatives, an even cofinal C, the radix, and
finally the shared Pell frame, in that order. These are precisely the
noncircular completeness choices of the retained parent proof.

## 6. Exact algebraic reductions

The source with the changed syntax and Pell center has 214 coordinates
and 154 quadratic rows. Substituting t=2+4z everywhere, deleting its
linear defining row and the t coordinate, gives 213 coordinates and
153 rows. The inverse restores that affine t.

Five common-Hessian projections give 208 coordinates and 148 rows.
For each projection direction v, every row Q_j has constant derivative
a_j along v. The selected coordinate of v and selected row slope are
both units. Writing x=y+sv, with that selected coordinate of y zero,
solves s=-a_r Q_r(y) integrally. Every remaining row becomes
Q_j(y)-a_j a_r Q_r(y), still quadratic. The certificates provide v,
the unit pivot, the omitted row, the restoration polynomial and the
complete renumbering. The independent checker reconstructs the result
by this row-combination formula rather than the producer's substitutions.

Finally, the 48 supplied integer shears and elementary row additions
are all invertible over the integers. The checker verifies both their
forward and reverse polynomial identities. They leave dimension and
degree unchanged while reducing the expansion from 7,527 to 5,987
monomials. A sum of squares after a row change need not be the same
polynomial; the common integer zero set is what is preserved.

## 7. Inherited boundary and computational scope

The numerical logical endpoints are the preserved
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The Pell
classification, signed common-frame/cap theorem, normalized remainder
decoding, generalized binomial CRT and single-conclusion Horn-flow
theorem are inherited from the specifically pinned arithmetic packet.
Their source and ordinary proof dependencies are retained in the complete
original parent archive bundled once with the enclosing deliverable.

The new work proves the sparse-calculus bridge, checks its exact local
interface, adjusts both growth and local size bounds, composes the
signed horizon, and certifies every new finite algebraic reduction.
Finite scripts authenticate coefficients and identities. They are not
a substitute for the unbounded theorems and do not create a consistency
witness. No new end-to-end proof-assistant build or externally reviewed
novelty/minimality claim is made.

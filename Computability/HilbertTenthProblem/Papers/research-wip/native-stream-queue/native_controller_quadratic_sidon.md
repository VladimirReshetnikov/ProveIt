# A cross-cell collision in the periodic Sidon-square proposal

A single product U^2 does not turn a fixed within-cell Sidon placement
into independent local quadratic tests. Its coefficients also contain
products from distinct cells, and those can occupy exactly the same
tested bit as a genuine local violation. The following counterexample
uses words satisfying the actual51-operation one-field half-mask
predicate and has no coefficient carries to obscure the issue.

This is a refutation of the stated coefficient-selection proposal, not
of all quadratic one-field compilers. No complete sub76 source or
uncharged bit extraction is asserted.

## 1. Fully typed positive input words

Take fixed d=8, B=256 and m=177. The forbidden bit positions of m are
{0,4,5,7}, so m is odd and has exactly d/2 set bits. Positions1 and3
are allowed. Use two Boolean payload bits a_i,b_i in every cell,

    U=sum_i (2*a_i+8*b_i)*B^i.

The fixed-position payload therefore obeys the mask of
[the one-field51 theorem](one_field_half_mask.md). For arbitrary p>=1,
choose N>4p and q=B^N, and consider

    U_good=2+8*B^(2p),
    U_bad=10*B^p.                                      (1)

Both are positive, even, and below q. Both have zero intersection with
m*J, where J=(q-1)/(B-1), and neither relies on an untyped interleaved
summand. The local predicate a_i*b_i=0 holds at every cell of U_good.
It fails at cell p of U_bad.

These tuples extend to the full positive one-field module: take
n=2^(4N) and the exact index r=(q-U)(q-1)+mJ. The inverse-packing
identity gives q<=r<q^2, odd r, and popcount(r)=12N, the valuation
required for scale n^3. The reviewed positive kernel converse supplies
the remaining coordinates. The checker corroborates these identities;
it does not materialize the enormous Pell witnesses.

## 2. Identical false and true quadratic flags

The square expands exactly as

    U_good^2=4+32*B^(2p)+64*B^(4p),
    U_bad^2=100*B^(2p)=(4+32+64)*B^(2p).                (2)

All displayed cell coefficients are below B, and N>4p ensures no
whole-word wrap. The intended mixed flag is bit5, since the cross term
of payload bits at positions1 and3 has value2*2*8=32. Therefore

    U_good^2 AND (32J)=U_bad^2 AND (32J)=32*B^(2p).       (3)

In fact the identical statement holds with the full mask mJ: the self
squares4 and64 occupy allowed positions2 and6, while the mixed flag32
is forbidden. Thus the supposedly local mixed flag rejects the valid
assignment as well as the invalid one. Looking only at this selected
quadratic flag cannot distinguish them.

The algebraic reason is independent of the numerical example. For
payload streams A=sum a_i B^i and C=sum b_i B^i, the mixed part of
the square is a fixed coefficient times

    A*C=sum_k [sum_(i+j=k) a_i*b_j] B^k.

Its coefficient at2p contains both the desired product a_p*b_p and
the unwanted product a_0*b_(2p). A Sidon condition on bit positions
inside a cell separates payload types, but does not separate cell pairs
having the same sum of indices.

Any fixed periodic spacing of active cells leaves this issue. Choose p
to be a multiple of that spacing: cells0,p,2p all lie in its permitted
phase, and the same collision remains. Increasing the fixed cell width
also does not help; the example is already free of carries.

## 3. A cyclic rotation of the second factor does not remove it

Suppose the proposed second factor is the whole-cell cyclic rotation
V=B^h U modulo(q-1). Choose N>4p+h. Then for both words in(1) no
wrap occurs even in the product, and

    U*V=B^h U^2.

The same mixed collision simply moves to cell2p+h. These are genuine
positive rotated copies, not arbitrary second fields. Hence replacing
U^2 by a product with a whole-cell rotated copy does not justify the
local coefficient interpretation either.

A reversal would change a sum of cell indices into a difference and
requires a different, fully paid construction. No free reversal,
selection of only diagonal products, or nonperiodic spacing of unbounded
cell indices is available in the proposed51+14+10 budget merely because
the multiplication itself costs one operation.

## 4. Scope and evidence

The [checker](native_controller_quadratic_sidon.py) verifies the complete
outer half-mask and inverse-packing hypotheses for both families, their
different local predicates, identical quadratic flags, and the no-wrap
rotated-product examples. It also checks the coefficient identity against
direct cell convolution on bounded arbitrary payload words.
The [receipt](native_controller_quadratic_sidon.json) is replayed by
default. Independent full proof, source, and default-replay review passed.
The result identifies a precise
failure of the naive periodic Sidon quadratic test; a different quadratic
compiler, including one that proves how cross-cell terms are handled,
remains an open constructive direction. The complete bound remains76.

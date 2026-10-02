# Independent audit of empty/star 2-by-3 cores and Boolean kernels

Verdict: **APPROVED**, October 1, 2026. Both notes are ordinary proofs, supplemented by the independent checks recorded here. Frozen earlier releases are unchanged.

## Scope

The fixed physical bipartite shores are `P union X` and `Q union Y`, with `|P|=2`, `|Q|=3`; both exterior blocks `P×Y` and `X×Q` are complete. The internal core H is any subset of `P×Q`. Activities are arbitrary independent nonnegative vertex activities, not independent edge weights and not arbitrary reversals of individual edges.

If the internal matching number is at most one, the signed physical support-monomer polynomial is real stable, and the support polynomial is negative-real-rooted and ULC at its actual surviving degree. Separately, every nonempty core mask has strict first and last order-five Newton inequalities at actual degree five. The seven noncomplete matching-two isomorphism types' middle gaps are not settled by these notes.

## The rank-three exceptional seed

The three private dummies ensure rank three even when the universal-tail set X is empty. With one exceptional tail p adjacent to heads 1 and 2, every triple is matchable except `{p,d1,d2}`. Hall obstructions of size one or two cannot occur: columns are nonempty and no two columns have union of neighborhoods of size one. A failing triple must avoid both the universal columns and d3, hence is precisely the displayed exception.

The exceptional block has three variables and the other block has `m=|X|+1>=1`, including d3. Thus m=0 never occurs in this seed. Its two-block diagonal is

`y[3m x^2+3 binom(m,2)xy+binom(m,3)y^2]`.

The discriminant equals `m^2(m-1)(m+7)/4`. For m>=3, the bracket is a positive multiple of two linear forms `x+alpha y`, `x+beta y`, where alpha,beta are nonnegative: their sum is the nonnegative middle coefficient divided by `3m`, their product is the nonnegative last coefficient divided by `3m`, and their discriminant is nonnegative. For m=1 the diagonal is `3x^2y`; for m=2 it is `3xy(2x+y)`. Each is stable.

The full basis polynomial is multiaffine and separately symmetric, and the diagonal uniquely determines it. Polarization with degree bounds `(3,m)` recovers it, including the cases where actual x/y degree is lower than the bound. The normalization is explicit: the diagonal term `3m x^2 y` polarizes to `e2(L0)e1(O)`, `3 binom(m,2)xy^2` to `e1(L0)e2(O)`, and the last term to `e3(O)`; terms exceeding a small block's size are absent.

I directly checked the primary definition and stability equivalence in Borcea–Brändén, *The Lee–Yang and Pólya–Schur Programs. I. Linear Operators Preserving Stability*, arXiv:0809.0401v3, Section 2.2 and Proposition 2.4, printed pages 10–11: https://arxiv.org/pdf/0809.0401. The operator is defined on a coordinate-degree-bounded space, so equality of degree and bound is not required. This precisely covers the polarization used here.

Empty exceptional neighborhoods give loops; singleton neighborhoods give a parallel extension of one private dummy, implemented by a variable sum; the universal neighborhood gives a uniform matroid. In the right-centered case, rank two has only singleton and universal nonempty exceptional neighborhoods. These are elementary-symmetric stable seeds. No blanket stability assumption for arbitrary rank-three transversal matroids is used.

## Weighted monomer transfer and one-vertex gluing

For positive activities, the stated basis-to-monomer transform has exactly one product of selected endpoint activities and the sign `(-1)^k` for each feasible endpoint support. Negative-reciprocal tail substitution and positive dummy scaling map the upper half-plane into itself. The denominators cancel because the basis polynomial is multiaffine. Zero activities follow from coefficientwise limits; the all-unused monomial has coefficient one and prevents the zero limit.

For a one-vertex union of two relations, consider a fixed feasible ordered support. If the common vertex p is unused, both restrictions are balanced. If p is used as a tail, the unique piece requiring it has one more selected head than selected non-p tails; if p is used as a head, it has one more selected tail than selected non-p heads. The other piece is balanced. Hence the support determines its piece assignment uniquely. Matching witnesses can remain nonunique without changing this conclusion. Conversely two feasible restricted supports using p at most once combine to a full support, with the product activity and matching-size sign preserved.

Using two monomer copies a,b, this bijection is the map `ab->z`, `a->1`, `b->1`, `1->0`. For a multiaffine polynomial it is exactly differentiation of the diagonal `f(t,t)` followed by `t=z/2`. Diagonalization, differentiation and positive scaling preserve stability or zero; the all-unused term excludes zero. This also verifies the factor 1/2 normalization. Both star-center cases decompose into the specified stable pieces meeting only at their center, while an empty core is a disjoint product.

The real-stable signed monomer diagonal is `x^n Gamma(-x^-2)`. Every nonzero Gamma root would give a monomer-diagonal root after solving `x^2=-1/t`; real-rootedness forces t negative real. The constant coefficient one excludes t=0. Newton then uses the actual degree, including all zero-activity drops.

## Boolean core kernel and strict outside gaps

For selected core sets I,J and a size-k support, the numbers of exterior selections are `k-|I|` and `k-|J|`. Exactly `|I|+|J|-k` internal core matching edges are needed. A matching of that size exists precisely under the note's Boolean rank condition; its leftover core vertices match all exterior selections via the complete blocks. This establishes the formula without witness multiplicities, including the W22 versus J22 distinction.

Independent expansion verifies every displayed W/J kernel and all six coefficients for all 64 masks. At degree five, all core activities and B,E,N,S are positive. For a nonempty core, W23=BE, hence gamma4 and gamma5 equal their complete-core values; gamma3 can only decrease on deleting edges. The approved complete-core strict last gap therefore transfers. The positive complete P×Y block contains a K2,2, giving strictness in the first gap by the same overcounting argument. The empty core has two disjoint complete bipartite components, already handled by the stability proof above.

## Supplementary exact checks and boundaries

The independent checker imports no producer code. It reconstructs all 64 Boolean kernels, compares literal Hall support sums in 2,304 weighted cases of degrees zero through five, and checks 216 formal endpoint-support gluing identities. These formal identities imply agreement of all monomer coefficients and arbitrary vertex products for the tested graphs, not merely one scalar polynomial evaluation. It also checks 714 triples in exceptional seeds with zero through eight universal tails and the discriminant identity symbolically. There are exactly 18 star/empty masks, five such orbits, and 13 total core orbits. All 126 tested nonempty-core degree-five last gaps are strict.

The proof is ordinary and covers all finite populations; these finite checks only corroborate the structural argument. No real-rootedness claim is made for matching-two cores. The complete-core nonreal example already prevents such a blanket claim. No novelty, minimality or proof-assistant-formalization claim is made.

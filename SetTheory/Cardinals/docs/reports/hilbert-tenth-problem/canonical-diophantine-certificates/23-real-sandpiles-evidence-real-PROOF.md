# A support-and-height-preserving real-orthant upgrade of the binary sandpile cubic

3 October 2026. This is a follow-on to the frozen binary finite-prism certificate,
not a change to Report 35 or to its approved source packet. No claim of a new
general real/Nat representation principle or literature-wide novelty is made.

## 1. Main theorem and exact scope

Fix a nonempty finite integer rectangular prism P in Z³, with ordinary
six-neighbor threshold 6. The natural-valued initial configuration η is stable
outside P. Its finite additions are all inside P; the executable input interface
uses a stable periodic background and finite nonnegative additions. Write V, E,
H for the numbers of interior sites, internal undirected edges, and exterior
six-face halo sites. Every halo site has exactly one neighbor in P.

Let Q be the exact binary finite-prism polynomial in the approved packet
`sandpile-certificate-composition-20261003/PROOF.md`, with compiler SHA256
bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2.
Its vertex variables are (z,ell,f,k,c,beta,g,h), its six edge variables are five
comparison selectors and a gap sigma, and it has one gap per halo site. Define

    Qreal = Q + sum_v f_v (k_v + c_v).

Present this polynomial by replacing the existing product f_v g_v with
f_v(g_v+k_v+c_v), leaving all other displayed summands unchanged. Then:

1. Qreal is an integer polynomial, orthant-nonnegative and of degree exactly 3
2. As sets of complete witness tuples in the same coordinate space,

       Z_{R>=0}(Qreal) = Z_N(Qreal) = Z_N(Q).

   In particular the entire real-orthant fiber is either empty or a singleton.
   Existence means exactly that a finite legal GLOBAL stabilization has binary
   odometer supported in P. It is not promised for every input or every prism
3. The variable count and displayed nonnegative summand count remain exactly
   W=8V+6E+H and J=8V+7E+H
4. The fully collected monomial support and the fully collected coefficient
   height are exactly unchanged. The only coefficient changes are
   [f_v k_v]: 2→3 and [f_v c_v]: 2→3
5. Under the original specified affine-expansion/evaluation convention, each of
   raw records, expansion multiplications, evaluation multiplications, and
   evaluation additions increases by exactly 2V

The prism and input are external compiler parameters. Arity grows with V. This
is not a fixed-arity unbounded representation, not a new finite-fold MRDP
statement, and not a computable halting cutoff. Zeros over all of R, approximate
floating-point zeros, and the unspecialized ten-variable vertex certificate are
not covered by this theorem.

## 2. The old local equations

Set u=k+c and r=k+2c+beta, without additional variables. At each vertex the
unmodified summands are

    (z+6u-sum_neighbors u-η)^2
    (z+ell-5)^2
    (f+k+c-1)^2
    (f+k)beta
    (k+c)(z-A-g)^2
    fg
    c(B-z-1-h)^2
    (f+k)h.

Replace fg by f(g+k+c). On an oriented internal edge v<w, δ=r_w-r_v, the old
comparison gadget, retained verbatim, is

    (lambda_lo+lambda_neg+lambda_eq+lambda_pos+lambda_hi−1)^2
    + lambda_lo(δ+2+sigma)^2 + lambda_neg(δ+1)^2 + lambda_eq δ^2
    + lambda_pos(δ−1)^2 + lambda_hi(δ−2−sigma)^2
    + (lambda_neg+lambda_eq+lambda_pos)sigma.

The five cases, in order lo/neg/eq/pos/hi, are respectively
δ≤−2, δ=−1, δ=0, δ=1, δ≥2. A_v and B_v are the same affine selector sums as in
the approved compiler. Their intended values are the counts of neighbors with
r_w≥r_v and r_w≥r_v−1. Halo summands are (η(x)+u_neighbor+q_x−5)^2.

Every term remains a square, a nonnegative linear weight times a square, or a
product of nonnegative linear forms. Replacing fg by f(g+k+c) introduces only
quadratic monomials. The old uncancelled k_v z_v² coefficient proves exact
cubic degree, even for a singleton prism.

## 3. The edge gadget was already exact over the real orthant

At a nonnegative real zero, the simplex square makes the five selectors sum to
1. Any positive selector forces its associated residual to vanish. Its five
possible equations place δ in the five pairwise disjoint sets

    (-infinity,-2], {-1}, {0}, {1}, [2,infinity).

Consequently at most one selector can be positive, hence exactly one equals 1.
The middle cases force sigma=0 by the last product. The extreme cases force
sigma=|δ|−2. In particular fractional differences in (-2,-1), (-1,0), (0,1), or
(1,2) cannot occur on an edge at a zero; fractional differences in either
extreme range may occur before the global rank argument.

It follows directly, over real ranks, that A_v and B_v have their intended
indicator-count meanings. Crucially,

    B_v-A_v = number of neighbors w with r_w=r_v-1.

The ten edge-selector pairproducts proposed initially are therefore unnecessary
for zero-set semantics. Their addition is harmless, but the theorem does not
need them.

## 4. Binary activity and finite rank descent

All displayed summands are nonnegative, so each vanishes at a real zero.
The category simplex and new product give

    f+u=1,   fu=0,   f>=0, u>=0.

Thus (f,u) is (1,0) or (0,1). If inactive, k=c=0 and (f+k)beta=0 forces beta=0,
so r=0. Inactive g,h also vanish. If active, f=0 and k+c=1, so

    r=1+c+beta >=1.

If c=0, k=1 and the beta product forces beta=0: r=1. Conversely r=1 forces
c=beta=0 and k=1. Thus every active vertex of rank r>1 has c>0. Its success and
preceding-failure terms force

    z=A+g >=A,          B=z+1+h >= z+1,

hence B-A>=1. Section 3 therefore supplies an adjacent vertex of rank r−1.
Because r−1>0, that predecessor is active.

The finite predecessor lemma now applies: in a finite active set S, with ranks
at least 1, if every rank greater than 1 has a predecessor of rank exactly one
less, every rank is an integer between 1 and |S|. Indeed, follow predecessors.
Ranks strictly decrease, so a vertex cannot repeat. If the chain did not stop
at rank 1, a further predecessor would be required after exhausting the finite
set. A chain with m edges ending at rank 1 gives starting rank m+1, and all
m+1 vertices are distinct. This proves both integrality and the bound. It does
not assume ranks are integers in order to terminate the argument.

Now categories themselves are one-hot. If k,c were both positive at an active
vertex, (f+k)beta=0 would give beta=0 and r=1+c in (1,2), contradicting rank
integrality. Thus rank 1 has k=1, while rank at least 2 has c=1, k=0 and
beta=r−2. This also gives a shorter local rejection of mixed active categories:
they would require a neighbor of rank in (0,1), while all ranks are 0 or ≥1.

Balance now forces z=η−6u+sum_neighbors u to be an integer, and stability forces
ell=5−z to be an integer. On active sites g=z−A; on rank≥2 sites h=B−z−1. All
other g,h values are forced to zero. Edge gaps and halo gaps are integer
residuals, too. Thus every coordinate of the full real zero is natural.

Conversely, every natural zero of Q has one-hot categories, so fu=0. It remains
a zero of Qreal, with the very same complete tuple. This proves both zero-set
equalities pointwise; there is no projection, hidden choice, or added witness.

## 5. Semantics, canonical ranks, and boundary cases

The approved natural theorem now transfers to real zeros. It can also be seen
directly: fire each active vertex once in increasing integral rank, in any order
within a tied rank. Just before v fires, its height equals z_v+6 minus the
number of its active neighbors not yet fired. That number is at most A_v, and
z_v≥A_v, so the firing is legal. The final interior state is stable by ell≥0.
Halo equations give stable final exterior heights; exterior heights only grew,
and sites beyond the halo never changed. Thus this is global stabilization.
Standard least action gives the unique odometer and endpoint.

The ranks are the unique earliest parallel support-burning rounds. Induct on
j. Rank-j sites are eligible by success. A site of rank r>j is ineligible because

    z_v < B_v = # {w: r_w>=r−1} <= # {w: r_w>=j}.

Thus the process burns exactly the prescribed layer each round. Every remaining
coordinate is a forced residual or category/selector, giving uniqueness of the
entire witness. The converse construction uses these unique parallel ranks for
the genuine binary odometer.

- Empty activity: all f=1, ranks/beta/g/h=0, edge equality selectors=1 and edge
  gaps=0; z=η, ell=5−η, and halo gaps=5−η. There is one witness if the input is
  already globally stable and none otherwise
- One-cell prism: there are no internal edges. A=B=0 excludes c>0 via the
  failure inequality. The only active rank is 1. Six distinct face-halo sites
  are still present
- Disconnected active support: predecessor chains remain within their active
  component. They terminate separately; simultaneous rank-1 roots are allowed
- Disconnected finite underlying graphs: the rank-integrality lemma does not
  require connectivity. The stabilization theorem additionally needs the usual
  sink-reachability/termination hypotheses in each component. The implemented
  rectangular prism already satisfies these hypotheses
- No activity beyond the prism: the initial exterior stability and all seed
  containment checks remain indispensable; neither is replaced by the rank
  argument
- Nonbinary true odometers: deliberately rejected. This upgrade does not
  restore the unspecialized general-odometer theorem

## 6. Exact monomial and coefficient invariance

For every vertex, the old fully collected coefficients of fk and fc are 2,
coming only from the category simplex square. Other summands involving f pair
it with beta, g, or h, never with k or c. Their increase to 3 cannot cancel an
existing monomial or create a new one. Distinct vertices give distinct monomials.
No other coefficient changes.

For an explicit height witness, the coefficient of kc is 86 at every vertex:
72 from that vertex's balance square, 2 from its category square, 2d_v from the
internal neighbors' balance squares, and 2(6−d_v) from its adjacent halo squares.
Their sum is 86. The weighted cubic terms do not add another quadratic kc term.
Because V>0 and this coefficient is unchanged, the old maximum absolute
coefficient is at least 86. Changing coefficients 2 to 3 therefore leaves the
maximum absolute coefficient exactly unchanged, not merely asymptotically
bounded. This count includes all inter-summand collisions.

## 7. Exact ledger under the original convention

Let R0 and X0 denote the approved raw-record and coefficient-expansion counts;
let A be the number of nonzero-height interior sites and L the number of halo
sites initially below 5. The merged Qreal presentation has

    W = 8V+6E+H                         (unchanged)
    J = 8V+7E+H                         (unchanged)
    plain square residuals = 3V+E+H     (unchanged)
    weighted square residuals = 2V+5E   (unchanged)
    product summands = 3V+E             (unchanged)
    raw records = R0+2V
    coefficient-expansion multiplications = X0+2V
    evaluation multiplications = 35V+76E+4H
    evaluation additions = 23V+63E+3H+A+L−1.

The convention counts each coefficient-times-variable multiplication, even for
coefficient 1, and adds terms by initializing with the first term. The old fg
product costs 3 multiplications and 0 internal additions; f(g+k+c) costs 5 and 2.
Both are one summand, so outer summation cost is unchanged. Expansion produces
3 rather than 1 coefficient products and records. This is an honest specified
implementation ledger, not an operation-optimality claim.

The unchanged local-owner collection algorithm works verbatim, since the added
monomials have the same vertex owner. Under the literal loader's η≤6, each
vertex contributes at most 957 raw records rather than 955, so a bucket sees at
most 7(957+3*173+6*10)=10752 raw records. This is constant record workspace,
not constant bit space. The polynomial's exact coefficient height remains that
of Q, so the old bound max(215V,773136) remains valid by coefficient invariance,
even though a naive recalculation of the local raw bound would be looser.

Safe literal-loader bounds become Rreal≤1536V, Xreal≤2416V, evaluation
multiplications≤287V, additions≤237V−1. Witness coordinate bounds and bit heights
are unchanged, now applying to every exact nonnegative-real zero because every
such zero is integral. The old loader height-evaluation costs remain charged.

For comparison, the originally proposed full-pair polynomial

    Qsharp = Q + sum_v(fk+fc+kc) + sum_edges sum_{i<j} λ_i λ_j

has the same full real zero set and natural fibers. Its old coefficients are
fk=fc=2, kc=86, and each same-edge selector pair=2, changing to 3,3,87,3.
Its collected support and exact cubic degree are unchanged, but exact coefficient
height need not be unchanged. With K=3V+10E, its raw and expansion counts increase
by K, evaluation multiplications by 3K, additions by K, and displayed product
summands by K. This is a valid but unnecessary larger upgrade. The separate
unmerged display Q+sum fu uses V extra summands, raw/expansion +2V, evaluation
multiplications +4V, additions +2V; it is algebraically identical to Qreal.

### Literal-loader corollary

For the already audited one-shot literal U15 loader, every global odometer is
binary. Therefore for each fixed admissible prism the merged polynomial has a
nonnegative-real zero exactly when that loader stabilizes with support inside
the prism, with exactly the same witness as its old natural certificate. Taking
the external family over all finite prisms preserves the old equivalence to
finite-tape U15 halting. No universal quantifier was replaced by a fixed-size
real polynomial, and no upstream universality theorem was reproved.

For the approved halt-bound prism with V≤C(n+T+1)² and
C=5426111451172075939316367360, the unchanged W and J bounds remain
26C(n+T+1)² and 29C(n+T+1)². The revised raw and coefficient-expansion bounds are
1536C(n+T+1)² and 2416C(n+T+1)². These remain parameterized bounds conditional
on an actual halting run, not a computable bound on T from n alone.

## 8. General lemma and limits

A useful abstract lemma isolated by the proof is finite predecessor rigidity:
if a finite set S carries real labels r≥1 and every r>1 has an edge to a label
r−1, then all labels are integers in [1,|S|]. No graph embedding, sandpile,
connectedness, initial data, or polynomial language is needed for this lemma.

Combining this lemma with (i) a binary-support selector gate, (ii) a disjoint
real-exact adjacent-difference gadget, and (iii) success/failure inequalities
whose count difference forces a predecessor yields an integrality mechanism
for this certificate. This is not a general claim that one-hot selectors alone
force all continuous magnitude variables integral. The public prior-art review
specifically records that distinction and an unspecialized counterexample.

## 9. Verification and provenance boundary

`real_certificate.py` implements merged, unmerged, and full-pair variants by
subclassing only an unchanged snapshot of the newly authored approved local
compiler, bundled under `approved_base/`, whose exact source
hash is checked before import. It suppresses bytecode writes to that dependency.
No upstream script is imported or executed. `exact_checks.py` has a separate
sparse polynomial engine which constructs and expands the formulas without
using the compiler's Summand.records method; it compares raw/global/local
collection, ledgers, degree, support, height, and exact rational evaluations.
It also exhausts category-support and edge-selector branches on specified tiny
instances using exact affine elimination and rational linear programming.
Accepted candidates are rechecked against every equality, inequality, and
original polynomial summand. Modified feasible branches are checked to have
all witness coordinates uniquely determined already by their affine equalities.
Returned feasible candidates are independently verified exactly. LP rejection
of an infeasible branch is solver-assisted evidence only: this packet does not
produce or independently check Farkas certificates for those rejections.
These finite computations corroborate the theorem; the proof above establishes
its all-real, all-finite-prism quantifiers.

The old spurious singleton real zero at η=1, z=0, ell=5, f=5/6, k=1/6,
c=beta=g=h=0, q_x=29/6 has Q=0 and Qreal=5/36>0. This is an explicit exact
adversarial regression, not a numerical near-zero test.

The targeted public comparison is in `PUBLIC_PRIOR_ART.md`. In particular,
ProveIt's quadratic-orthant-certificate work already contains strong real
one-hot gates and an all-real-zeros-natural theorem for trace encodings.
Manuscripts 16/19 contain the reused support-burning and canonical-rank theory.
The limited contribution claimed here is the specific merged binary-sandpile
cubic strengthening, its rank-descent proof, and its exact coefficient/count
invariance. No absence claim beyond the reviewed sources is made.

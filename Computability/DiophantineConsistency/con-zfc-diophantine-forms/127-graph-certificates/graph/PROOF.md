# Shared graph flows for height-one quartics

Independent mathematical audit, 24 October 2026.

This note develops an elementary replacement for the row-energy construction in
the incoming height-one compiler. It proves coefficient height one and exact
zero-set correspondence; it does not supply an independent consistency
calibration for the source system. The relevant source is the normalized
quadratic system of 572 rows and 2,378 signed term occurrences from the
519-integer direct C222 equation.

## 1. Half-incidence energy

Let G be a finite undirected simple graph with an arbitrary orientation of its
edges. Attach an independent formal symbol t_e to each edge. Write d_v for its
signed incidence sum at vertex v: an outgoing edge contributes t_e and an
incoming edge contributes -t_e. Then

    E_G(t) = (1/2) sum_v d_v(t)^2

is a polynomial with integer coefficients. Each t_e^2 occurs at the two
endpoints, hence has coefficient one after division by two. Distinct edges of
a simple graph have at most one common endpoint. Accordingly, t_e*t_f has
coefficient +1 or -1 if they meet, and zero otherwise. Thus the fully collected
coefficients of E_G are all in {-1,0,1}. Also E_G is nonnegative over the reals,
and vanishes precisely when every d_v vanishes.

The absence of parallel edges is necessary. Two parallel edges have two
common endpoints; their off-diagonal coefficient can be +2 or -2.

## 2. Elimination of tree flows

Partition G's vertices into connected blocks. Each block's internal edges
form a tree and carry free integer variables w_e. All edges between blocks
carry specified integer values c_e. Then there is an internal flow making
all d_v zero if and only if the signed sum of the prescribed external flow
incident to each whole block is zero. Whenever the condition holds, the
internal tree flow is unique and integral.

Proof: summing divergences over a block cancels its internal edges, proving
necessity. For sufficiency, choose a root and eliminate leaves. At a leaf,
there is one remaining internal edge, whose coefficient in the divergence
equation is +1 or -1. Its integer value is uniquely determined by that
equation. Delete the leaf, incorporate its edge value at the parent, and
continue. The final root equation is the block-sum condition. This also
proves uniqueness and integrality. Equivalently, every tree-edge flow is a
signed sum of prescribed flows crossing its rooted subtree boundary.

The latter description shows that free flows are integer linear forms in
the prescribed values whenever the block-sum conditions hold. The same
linear formulas make sense away from solutions, but leave the root
divergences equal to the block residuals; this distinction matters for any
claimed polynomial-map identity away from the zero set.

## 3. One shared hub block for all source rows

Let the normalized source rows be

    R_r = sum_(i=1..s_r) epsilon_(r,i) m_(r,i),

where each epsilon is +1 or -1. Choose a positive integer H. Create a hub
block containing H vertices, connected by a tree. For source row r create
a separate block of b_r=ceil(s_r/H) vertices, also connected by a tree.
Place the s_r term occurrences on distinct edges between its row block and
the hub block; the capacity b_r*H is sufficient. Orient every such edge
from the row block toward the hub block and give it value epsilon*m.

The sum of divergences over row block r is exactly R_r. The hub-block sum
is -sum_r R_r. Therefore Section 2 gives the equivalence

    exists integral internal flows: E_G = 0
       iff every R_r = 0.

All required free tree flows are unique once the source term values are
fixed. Their number is

    F(H) = H - 1 + sum_r (ceil(s_r/H) - 1).

At most s_r source edges are needed in row r, with no requirement that all
hub vertices be incident to a prescribed edge. Every vertex still belongs
to its stipulated internal tree; isolated *source incidence* is harmless.
For an explicit assignment, number the row's terms from zero and attach
term i to row vertex floor(i/H) and hub vertex i mod H. Distributing edges
more evenly among hubs changes the monomial count but not this proof.

The original source's row-size distribution is

    {2:230, 3:113, 4:94, 5:15, 6:38, 7:28, 8:11, 9:2,
     10:9, 11:16, 14:2, 15:1, 16:8, 22:2, 25:1, 29:1, 63:1}.

Finite evaluation of F(H) for 1<=H<=63 gives minimum 22 at H=16.
Here the hub tree uses 15 variables and the source-row trees use seven.
H>63 cannot improve this, because F(H)=H-1>=63. This minimum is only
within the one-hub-block architecture, not among every possible encoding.

For comparison, separate star constructions require sum_r(s_r-1)=1,806
flow variables. Separate optimally balanced bipartite row constructions
require sum_r(ceil(2*sqrt(s_r))-2)=1,205. Sharing hubs reduces the number
of auxiliary flow coordinates very substantially, while potentially
increasing the number of quartic cross terms at high-degree hub vertices.

## 4. Shared factors without coefficient collisions

Each occurrence i receives its own fresh private coordinate a_i. Shared
factor representatives s_v are distinct from all private coordinates and
from all flow coordinates. Introduce one separate shared unit u.

Represent a quadratic normalized term v_j*v_k by

    m_i = a_i*s_(v_k),

where a_i is an alias of v_j. Either orientation may be chosen independently
for each term. A linear term v_j becomes a_i*u, where a_i aliases v_j.
A constant term 1 also becomes a_i*u, with a_i a private unit alias. All
source monomials remain homogeneous of degree two and every one has exactly
one private factor which appears in no other source monomial.

The private factor makes the following substitution collision-free:

* A square m_i^2 contains a_i^2 and is unique to occurrence i.
* A product m_i*m_j with i!=j contains the unordered private pair a_i,a_j;
  it is unique to that occurrence pair, even when the shared factors agree.
* A product m_i*w_e contains private a_i and flow w_e, and is unique to
  that pair. It has degree three.
* Flow squares and flow cross products use only the flow namespace and
  have degree two.

Consequently, substituting these monomials into E_G preserves coefficient
height one. Every variable has individual degree at most two: private
variables occur at most squared; a shared factor can occur twice when two
source edges share it; flow variables occur at most squared. Total degree
is four as soon as at least one source occurrence exists.

An optional square-alias variant treats an occurrence v_j^2 as m_i=a_i^2
instead of introducing a shared representative solely for its second
factor. Each private marker then has exponent one or two in its own m_i
and is absent from every other m. A square m_i^2 has exactly one private
marker, with exponent two or four; a cross product m_i*m_j has two distinct
private markers. These patterns still identify every unordered source-edge
pair, so all coefficient and zero-set conclusions remain unchanged. The
individual-degree bound in this variant is four, while total degree stays
four. Shared representatives used by other nonsquare terms are retained.

For every logical normalized variable v, collect its private aliases and
its shared representative if one was needed. A singleton needs no
constraint. A class of size two receives one fresh dummy alias. For every
resulting class a_1,...,a_k with k>=3 add

    C = sum_i a_i^2 - sum_i a_i*a_(i+1), with cyclic indices.

Twice C is the sum of the consecutive squared differences. It is
nonnegative, vanishes exactly when every class value agrees, and has
coefficients +1 and -1 because the cycle has at least three vertices.
Classes are disjoint. Their quadratic terms contain no flow coordinates,
so cannot collide with quadratic terms from E_G.

Collect u and all private unit aliases into one unit path. If necessary
append fresh unit aliases so that the path has at least two vertices.
For u_1,...,u_k use

    U = 1 + sum_i u_i^2 - u_1 - u_k
        - sum_(i<k) u_i*u_(i+1).

Twice U is (u_1-1)^2 + sum_(i<k)(u_i-u_(i+1))^2 + (u_k-1)^2.
It vanishes precisely when all these unit aliases equal one. Its constant
term is one and it has coefficient height one. Its variables belong to
no ordinary alias class, so its coefficients cannot collide with the
alias-cycle terms. The complete polynomial is

    P = E_G + sum_alias_classes C + U.

It is nonnegative over the reals, has coefficient height one, and its
integer zeros correspond bijectively to zeros of the normalized source:
alias values, unit values, and internal tree flows are all uniquely
determined. If coefficient normalization uses monic topological definitions,
this bijection composes with the original source system's zero-set bijection.

## 5. Simpler audited variants

The shared-unit version with two private factors on quadratic terms needs
3,548 logical factor aliases, 107 private constant aliases, the one shared
unit, 297 equality-cycle dummies, and 22 flows: 3,975 variables. This count
precedes the stronger shared-second-factor orientation optimization above.

If a normalized square is represented by a single private alias squared,
the same collision argument remains valid but individual degree can be
four. The source has 378 such squares. Its logical factor-alias count then
becomes 3,170 and its two-member-class dummy count becomes 294. With shared
unit and 22 flows, the corresponding count is 3,594. This alternative is
not needed if the stronger shared-factor compiler gives a better count
while retaining individual degree at most two.

## 5a. C4-free reuse of the private factors

The per-occurrence private-coordinate condition can be weakened. Regard
the nonsquare source monomials a*s as edges of a bipartite factor graph
between private-side aliases A and shared-factor representatives S. Permit
several occurrences to use the same private alias only when they represent
the same logical first factor, their shared factors are distinct, and the
factor graph contains no cycle of length four. Square-loop monomials a^2
remain on private aliases that occur in no other source monomial.

The no-four-cycle condition means that no two distinct private aliases have
two common shared-factor neighbors. It can be checked by recording every
unordered pair of shared neighbors of each private alias and requiring
that no pair is recorded twice.

Claim: every product of two source monomials determines its unordered pair
of source occurrences uniquely. For nonsquare monomials, a competing
factorization must use the same multiset of private factors and the same
multiset of shared factors. With a repeated private or shared factor the
edge pair is forced, since duplicate edges are forbidden. With distinct
private factors a,b and distinct shared factors s,t, the only alternative
is (a*s)(b*t)=(a*t)(b*s). All four factor edges would then be present,
contradicting the no-four-cycle condition. A square-loop occurrence uses
a private coordinate absent from every other monomial, so any product
containing that occurrence is also uniquely determined. This proves the
claim in all cases.

Source-edge/flow-edge products are unique as well: the flow variable
identifies its edge and every source monomial is distinct. Thus the full
half-incidence energy still has coefficient height one after factor
substitution. Alias-cycle terms occupy the separate quadratic alias
namespace exactly as before.

Reusing an alias restricts neither direction of the zero-set correspondence:
all occurrences represented by that alias are copies of the same logical
source variable and were already forced equal at every old zero. Rebuild
each logical alias cycle on the distinct surviving coordinates, inserting
one dummy only when its new size is two. The forward source lift assigns
the common logical value, and the reverse map reads that same value.

The deterministic experimental compressor scans occurrences in source
order. It keeps square-loop aliases separate. For a nonsquare occurrence
with shared factor s, it may join an existing private group for the same
logical variable if s is new to that group and every pair {s,t} with an
existing group neighbor t has not appeared at any previous private group.
Among admissible groups it chooses a largest group, breaking ties by its
creation index. Otherwise it creates a fresh group. This construction
maintains the simple C4-free factor graph by induction. It makes no
optimality claim.

On the independently checked 442-source, H=128 square-alias artifact,
this reduces 1,969 private occurrences to 1,752 private groups, a saving
of 217 coordinates. Rebuilding equality cycles removes another 61 dummies.
The final polynomial therefore has 2,215 variables, 30,468 monomials,
degree four and height one. This compares with 2,493 variables and 31,186
monomials before the C4-free compression. The individual-degree bound is
four because square-loop aliases remain present. These are finite
artifact counts checked by independent full coefficient expansion.

## 6. Scope and checks still required

The proof above is unbounded ordinary finite algebra and graph theory; it
does not rely on sampling or a consistency assumption. A concrete release
must independently verify every normalized row, edge assignment, simple
graph invariant, alias class, unit path, and collected polynomial
coefficient. Any concrete monomial count, dimension after orientation
optimization, or full-polynomial hash requires the actual emitted artifact.

The exact original-value identity P(L(x))=sum R_r(x)^2 need not survive
the shared hub construction off the zero set. With canonical rooted-tree
flows, the remaining divergences are one R_r per row block and
-sum_r R_r at the hub root, so the graph energy becomes

    (1/2) [sum_r R_r^2 + (sum_r R_r)^2],

not generally sum_r R_r^2. This is itself a useful exact identity and has
integer coefficients. Alias and unit energies vanish under the forward
substitution. Both expressions have the same zero set over the integers
and reals, but the different value identity must be stated accurately.

The graph construction resembles standard incidence/Laplacian quadratic
forms. No worldwide-priority claim is justified merely because the
particular compiler combination is absent from the inspected packets.

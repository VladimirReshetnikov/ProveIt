# Partial partitions give an FPT dual-forest selector

## Scope and exact theorem

Input: a connected finite multigraph D with one graph edge per row of a
finite nonnegative integral matrix A. Ineligible rows may instead have no
graph edge; loops cannot be selected in a forest. A selected spanning tree
deletes its rows. A unit-column peel removes the unique row whose positive
occurrence has total one in a column of the current row restriction.
We decide whether some spanning tree leaves a completely peelable matrix.
This is a restricted geometric-certificate decision, never a knot verdict.

Call a column active if at least one entry is one. Let E be the active
columns supported on more than two rows, and let U be the union of their
row supports. Put u=|U|. The decision takes at most Bell(u+1) polynomial
graphic/partition matroid-intersection calls, with O((u+1)m) candidate edge
copies in each call, and polynomial preprocessing in the encoded input.
Consequently the bound is 2^{O(u log(u+2))} poly(N). For k exceptional native
columns, each of shape (1,1,1), u<=3k. No bound on the number of three-handles
is needed. No global bound k=O(log n) is proved or assumed.

## Baseline implication digraph

Ignore inert columns (no entry one); these cannot produce a peel under any
row deletion. Ignore the exceptional columns for now. On all row labels
form a directed graph P. A singleton active column at r makes r an automatic
seed. A two-row active column on r,s gives s->r exactly when the entry at r
is one, and gives r->s exactly when the entry at s is one. Let Z denote the
automatic seeds. As established in the prior two-row theorem, deleting Q
and applying only the baseline columns activates exactly Reach_P(Z union Q).

Each exceptional column with support V yields the implication
V\{r} -> r for every r in V with entry one. These implications are exact:
they fire precisely when r is the only remaining supported row of that
column and its entry is one. A column used for a peel has no other live
owner; its continued appearance in the implication system therefore cannot
cause an additional spurious peel.

Let S_1,...,S_q be the source strongly connected components of P that
contain no automatic seed and are disjoint from U. Each S_i MUST be hit by
the deleted tree rows. Indeed it has no incoming baseline implication, no
automatic seed, and no exceptional implication can target a row in it.
Conversely, one selected row in S_i activates the entire SCC and all its
baseline descendants. Write M=union_i S_i. Define B=Reach_P(Z union M).
The notation seeds all of M only as an activation convenience: each group
will actually be supplied with a single forest representative.

All other source SCCs either contain an automatic seed or intersect U.
It follows that a set of initial tree seeds, hitting each S_i, eventually
activates every row if and only if it activates every row of U. For the
reverse direction, all source SCCs have then become active, and every SCC
in a finite condensation DAG is reachable from a source.

## Finite interface closure

For each row r, define sigma(r)=Reach_P(r) intersect U. On subsets of U
define HClosure to close under: (a) u->v whenever u,v are in U and v is
reachable from u in P; and (b) all exceptional implications above. Let
B_U=B intersect U. For any tree seed set Q with at least one row in every
S_i, its eventual active U set is exactly

  HClosure(B_U union union_{r in Q\M} sigma(r)).

Proof: every displayed seed and implication is available in the full
system, giving one inclusion. Conversely, follow a full activation trace.
A maximal baseline path from a seed in Z union Q contributes a listed
signature; a baseline path from an exceptional head starts at a U row and
is represented by the reachability rules on U. Every exceptional rule is
listed verbatim. Induction on the number of exceptional firings gives the
opposite inclusion. Thus eliminating the baseline vertices does not assume
any geometric move beyond the original raw peeling rules.

## Enumeration and cloned matroid intersection

Enumerate a subset U0 of U and a set partition Pi={B1,...,B_l} of U0 into
nonempty blocks; the empty subset has the empty partition. Reject the
case unless HClosure(B_U union U0)=U. For every block form the candidate
group G_j={r outside M : B_j subset sigma(r)}. Ineligible edges and loops
can be omitted. Seek one distinct representative from every group in

  S_1,...,S_q,G_1,...,G_l

such that all representatives are graphically independent. The groups G_j
may overlap. This is Rado's independent-representatives problem, solved
with ordinary graphic/partition matroid intersection after cloning: each
allowed membership (r,group) is a graph edge with the endpoints of r and
the color group. Parallel copies of a single original nonloop edge cannot
both lie in a forest. Thus graphic independence enforces distinct original
rows, as well as forest independence; the partition matroid enforces one
membership per group. There are at most m+(u*m) copies: the mandatory SCC
groups are disjoint and each other row appears in at most u block groups.

If representatives exist, extend their forest Q to a spanning tree T in D,
and recompute a peel order on A with the T rows deleted. Output that tree
and order, for independent replay. Extending the forest can only add row
deletions; peelability is hereditary under further row deletion.

## Soundness

Every mandatory SCC has a selected representative. Each guessed block is
contained in the actual signature of its representative. Therefore Q's
actual activation contains B_U union U0 and its entire HClosure, which is
U by the explicit test. Hence Q activates all source SCCs and all rows.
Equivalently A\Q is completely peelable. Tree extension preserves this,
and the final emitted positive trace is checked directly on A\T.

## Completeness

Suppose a successful tree T exists. Choose one of its edges in each S_i;
these choices are possible by necessity. Put

  U0 = union_{r in T\M} sigma(r).

Its interface closure together with B_U is U, by exactness above. For
each u in U0 choose one witnessing edge r(u) in T\M with u in sigma(r(u)).
Partition U0 by equality of r(u). The resulting nonempty blocks B_j have
distinct representatives among T\M, and B_j is contained in the signature
of its witness. These representatives, together with the chosen mandatory
ones, form a subset of the tree T and are independent. This enumerated
case therefore succeeds. In particular one never needs more than u extra
representatives; choosing u independent witnesses is a consequence of
an actual successful tree, not an assumption that arbitrary sources can
be replaced without preserving independence.

## Counting and bit complexity

A partial partition of U is equivalent to a partition of U union {star}:
the block containing star records the omitted elements, and all other
blocks are Pi. There are exactly Bell(u+1) such objects. By assigning each
ordinary element either to the distinguished block or to the least
ordinary label of its block, Bell(u+1)<= (u+1)^u. This gives the displayed
FPT bound. Input reading is polynomial in the binary integer encoding;
counts may be capped at two for this decision, but actual unsaturated
counts are required for any separately asserted geometric parity theorem.
Reverse reachability from each of the u interface rows computes all
signatures sigma(r): a row r receives target u exactly when it can reach u
in P. Forward reachability from interface rows computes the interface
reachability rules. Signature candidate groups use ordinary subset tests.
The matroid-intersection algorithm is the classical shortest augmenting
path algorithm reused from the prior Dual Forest Normalization package.

This theorem applies to arbitrary matrices satisfying the stated parameter
bound, including some matrices not geometrically realizable. In a native
authenticated core it is a valid finite selector only after the separate
source/cocore incidence and tree-cancellation theorems authenticate its
input. The new contribution is the bounded-interface reduction and partial
partition enumeration; raw peeling, Rado's theorem, and the polynomial
two-row solver are prior results.

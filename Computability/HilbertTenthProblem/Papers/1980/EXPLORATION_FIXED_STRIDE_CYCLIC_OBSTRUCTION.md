# Fixed-stride cyclic local certificates have a finite-state obstruction

This note rules out one way of removing the variable temporal stride from
the [77-operation construction](FIXED_RAW_UNIVERSAL_77_PROOF.md). If a proposed
replacement is defined **solely** by a fixed finite alphabet, finite local
constraints, existence of a finite cyclic word, and two unique markers at
raw distance x, then fixed strides give an effectively ultimately periodic
set of positive inputs. Strides computed from x by a terminating algorithm
give a decidable set of inputs. Neither can represent every recursively
enumerable set in that interface.

The result concerns the local-language representation, not an unrestricted
arithmetic lower bound. Additional unbounded nonlocal arithmetic constraints,
an unbounded alphabet, or a separately certified long-range correspondence
can evade its hypotheses. In particular, no assertion is made here about
all possible polynomial substitutions for an arithmetic period coordinate.
The sound 77 source is unchanged.

## 1. Exact interface, including short cycles

Fix a nonempty finite alphabet Sigma, a finite set D of integer offsets
containing0, and a relation R on Sigma^D. A word c indexed by Z/N is locally
valid when, at every i, the tuple (c[i+delta])_(delta in D) belongs to R.
Repeated positions are interpreted modulo N, including when N is smaller
than the span of D. Several fixed local tests can be combined into R.

Let S and E be disjoint subsets of Sigma, the Start and End predicates, and
let O=Sigma\(S union E). For a positive raw input x, the represented property
is the existence of N>x and a locally valid cyclic word with

    c[0] in S, c[x] in E, c[i] in O for all other residues i.       (1)

Thus marker symbols may have finitely many internal variants, such as
ignored dummy bits. Both marker occurrences are unique. A known semantic
bijection that establishes this uniqueness, as in the 77 construction,
can be used before applying the present obstruction.

## 2. A finite graph that represents every cyclic length

Put a=min D, b=max D and ell=b-a. The vertices of a directed labelled
multigraph G are the words in Sigma^ell. For every block
(z[0],...,z[ell]) whose entries at positions delta-a pass R, put an edge

    (z[0],...,z[ell-1]) -> (z[1],...,z[ell]),

labelled by the letter z[-a]. Classify this edge as S, E or O by that
label. If ell=0 there is one empty-word vertex, and the permitted letters
give its loops. The graph has V=|Sigma|^ell vertices, even if some are
unused. Parallel edges are retained conceptually.

Locally valid cyclic words of length N correspond to length-N closed walks
with their edge labels in cyclic order. To prove the converse without a
long-cycle assumption, write z_i[j] for the block of the i-th edge. The
overlap relation gives z_i[j+1]=z_(i+1)[j], with edge indices modulo N.
Consequently, if c[i]=z_i[-a], then

    z_i[j]=c[i+a+j] modulo N.

This proves both the required local relation and the stated labels for
every N>=1, even when N<ell. The forward map takes precisely these blocks
from a cyclic word. There is no free-boundary or distinct-position premise.

For x>=1, a closed walk satisfying (1) is exactly a concatenation of:

* one S edge u->v;
* x-1 O edges from v to w;
* one E edge w->z;
* any number of O edges returning from z to u.

The last path may have length0. Its reachability is decidable in the finite
O-edge subgraph. If it exists, a shortest such return path has length at
most V-1. Thus every positive instance has a witness satisfying

    x+1 <= N <= x+V.                                             (2)

Shortening that return path is legitimate because the resulting object is
still a closed walk in the same graph; the preceding short-cycle proof
then reconstructs a valid cyclic word and preserves marker distance x.

## 3. Fixed strides give a unary regular language

Let A be the Boolean adjacency matrix of O edges. Form the fixed set T of
ordered pairs (v,w) for which there are an S edge u->v and an E edge w->z
with an O-edge return path from z to u. Then the exact membership test is

    x is accepted iff (A^(x-1))[v,w]=1 for some (v,w) in T.        (3)

This already gives a finite unary automaton: choose a pair in T, start at
v, follow x-1 O edges, and require endpoint w. Equivalently, the finite
sequence of Boolean matrices I,A,A^2,... eventually repeats, and every
subsequent matrix follows by multiplying by A. Formula (3) is therefore
effectively ultimately periodic. One can compute a threshold and period
by waiting for a repeated matrix; the crude state bound is 2^(V^2).

This theorem applies to any fixed finite list of offsets, however large
their free numerical values. A fixed number of finite phase tracks or
finite cell decorations can be incorporated into Sigma and does not
change the conclusion when every dependency remains at a fixed offset.
It does not cover position-dependent routing whose correctness requires
an additional unbounded nonlocal condition.

## 4. Input-computable strides still give a decision algorithm

Suppose instead that the finitely many offsets are computed from x by a
terminating algorithm; the alphabet, marker predicates and local table
remain fixed. For each input, construct its finite graph G_x and apply
the return-path test and (3) at that x. Equivalently, (2) bounds the
cyclic lengths that need be considered for that input. This is a total
decision procedure, regardless of how large the graph becomes.

No uniform ultimate-periodicity claim is made in this case: G_x itself
can change with x. The conclusion is decidability, which is already
incompatible with a uniform claim for arbitrary recursively enumerable
sets, including undecidable ones.

The same conclusion holds if the stride remains existential but is bounded
by a total computable H(x): construct the finitely many possible graphs.
One may also impose a total computable minimum word length N>=M(x),
including N>h(x). Put t_min=max(0,M(x)-x-1). In any existing return path,
retain its first t_min O edges and replace the remaining return by a
shortest O path. This preserves the minimum length and gives the complete
bound

    max(x+1,M(x)) <= N <= x+t_min+V.                              (4)

For a graph decision, replace O reachability in Section3 by A^t_min times
its reflexive transitive closure; equivalently use a counter capped at
t_min before permitting the return to end. Every value is computable
from x. If the minimum M is fixed, only the finitely many inputs x<M-1
can alter the original language, so fixed-stride ultimate periodicity
is unchanged. These changes do not supply unbounded computation space
at a fixed raw input.

For the helical interface this rules out replacing the existential stride
h by a fixed h, or by a computable function h(x), while retaining only
the finite local constraints and marker interface. Using the already
decoded endpoint power to set the temporal shift to x is one example.
A temporal shift N-j is the same cyclic offset as -j and is covered too
when j is fixed or computed from x. These are statements about the
resulting offsets, not claims that arbitrary arithmetic expressions in q
automatically decode as such offsets.

A queue or space-filling serialization can still be a useful alternative,
but its unbounded positional matching cannot simply be assumed to follow
from finitely many fixed-offset local checks. The missing matching or
unbounded stride must have its own mathematical and paid implementation.

## 5. Exact checks and their boundary

The [checker](../verification/explore_fixed_stride_cyclic_obstruction.py)
and adjacent JSON receipt independently compare direct cyclic local
evaluation with the graph's closed walks, including cycles shorter than
the offset span. They compare (3) with direct marked-word enumeration
through the proved complete bound x+V for several finite relations,
compute repeated Boolean matrices, and check varying computable offsets
by rebuilding the graph, with additional input-computable minimum lengths.
A nontrivial example accepts precisely even
marker distances, exercising both accepting and rejecting outcomes.

These finite checks support the general proof; they are not an enumeration
of all local tables or a lower bound on straight-line certificates. No
source operation count is claimed. The default CLI compares a fresh result
to the saved receipt and never writes; regeneration requires `--write`.

Review status: author and independent complete proof/source reviews pass.
Fresh default verification matches the saved receipt, including the
computable minimum-length extension. An independent prefix/return automaton
also agrees with direct cyclic evaluation on additional finite examples.

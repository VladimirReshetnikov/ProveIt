# Formal review of the region-parameterized reachability theorem

## Precise bounded family

Let T be a generalized face-paired triangulation with n >= 1 labelled
tetrahedra. Its face-adjacency graph G has one vertex per tetrahedron and
an edge for each paired pair of faces. Loops and multiple edges are
permitted; the number of distinct neighbours is at most four.

Fix nonnegative integers r,c,U. A trace is in the region-bounded family
if it consists of the repository's legal formal 2-3 and 3-2 replacements,
contains at most U total 2-3 moves, and there is a subset F of the original
tetrahedra such that:

1. |F| <= r;
2. G[F] has at most c connected components;
3. every original tetrahedron consumed anywhere in the trace belongs to F.

The third condition says that the actual consumed initial footprint is
contained in F. It need not equal F. In particular, an actual footprint
can have more than c components while lying in a connected allowed region
F: some intervening original tetrahedra can survive. The theorem therefore
uses a cover of the footprint by an allowed region, not an assertion that
the actual footprint itself has at most c components.

The empty region is permitted and covers the empty trace. If c=0 or r=0,
the empty region is the only possible region.

## Theorem: exact region-bounded reachability

Assume that local move production, cocycle transport if present, and the
chosen isomorphism-invariant endpoint predicate can each be computed in
polynomial time in the current triangulation and marking bit size.
There is an exhaustive search of the region-bounded family using

    (r+1)(c+1) n^c 32^r 11^(3r+5U)

executions or trace representatives, with polynomial overhead in
n+r+U+B, where B is the initial cocycle coordinate bit length. Consequently
the running time is

    n^c 2^O(r+U) poly(n+r+U+B).

For a fixed F of size i, the factor for executions/trace representatives
is at most 11^(3i+5U). Every execution is sound, and every permitted target
endpoint is reached up to the explicit tetrahedron/vertex isomorphism and
the induced transport of its marking.

If the endpoint predicate is not polynomial, multiply the bound by its
worst-case cost on n+U tetrahedra and B+U+O(1) coordinate bits.

### Proof: number of original allowed regions

First consider a connected set A of k >= 1 vertices. Its canonical root
is its least-labelled vertex. Fix a deterministic spanning tree of G[A]
rooted there and traverse that tree depth-first, traversing each tree edge
twice. The walk has length 2(k-1). Record, at every step, which of at most
four local face ports is crossed. The starting root together with this
word determines the visited vertex set and therefore determines A. Thus
there are at most

    n * 4^(2(k-1)) = n * 16^(k-1)

connected k-vertex sets. Self-loops and repeated neighbours do not harm
the bound: there remain at most four local choices, and the encoding
of any genuine chosen spanning-tree walk is valid.

For an i-vertex set with j >= 1 components, order the components by their
least vertex. Encode their j roots, their positive sizes k_1,...,k_j
summing to i, and the corresponding walks. There are at most n^j root
lists, binom(i-1,j-1) positive compositions, and 16^(i-j) walk lists.
Hence the number of such sets is at most

    n^j binom(i-1,j-1) 16^(i-j) <= n^j 32^i.

Sum over 1 <= i <= r and 1 <= j <= min(c,i), and add the empty set.
For n >= 1 this is at most

    (r+1)(c+1) n^c 32^r.

This is intentionally coarse. It is a rigorous uniform bound including
the degenerate cases and suffices for the asymptotic theorem.

### Proof: commitments for a fixed allowed region

Every initial tetrahedron outside F receives the forced commitment idle.
The i tetrahedra in F and every subsequently born tetrahedron receive
one of eleven symbols: idle, a local edge (six choices), or a local face
(four choices). A legal 3-2 move is ready when all three participating
tetrahedra select their local copy of its central edge. A legal 2-3 move
is ready when both tetrahedra select the copies of its common face.

At most one ready move uses any tetrahedron, because a local edge or
face port uniquely identifies the relevant move. Consequently all ready
moves have disjoint consumed supports and commute relative to boundary.

Choose a fixed deterministic scheduler of ready moves. It never consumes
an initial tetrahedron outside F, and it never uses more than U upward
moves. Suppose it uses u <= U upward and d downward moves. At least n-i
initial tetrahedra survive, whereas the current count is n+u-d. Therefore

    n+u-d >= n-i,  so d <= i+u.

The number of freely assigned incarnation symbols is the number of
initially allowed tetrahedra plus all output tetrahedra:

    i + 3u + 2d <= 3i + 5u <= 3i + 5U.

Thus fixed-length words of N_i=3i+5U eleven-symbol letters suffice;
unused suffixes can be ignored. Enumerating these words runs the
deterministic scheduler at most 11^N_i times. A variable-length prefix
tree has at most (11^(N_i+1)-1)/10 nodes, which differs only by a constant
factor.

For completeness, fix any permitted target trace contained in F. Give
each incarnation its eventual consuming port in that trace; give each
final survivor idle. Any currently ready move equals the first future
target move touching its support. Until such a touch, its common face
or full degree-three central-edge star remains unchanged. That first
touch must use the already selected local port, so is exactly the ready
move. All earlier target moves have disjoint support, and the ready
move can be commuted left across them. Repeating this operation yields
the scheduler's deterministic execution. Transport local commitments
through the explicit relabellings arising in these commutations.

The output execution is equivalent to the target trace under commuting
adjacent disjoint-support replacements. It has the same original
consumed tetrahedra and the same upward count, and its endpoint is the
same marked triangulation up to the induced isomorphism. Final idle
symbols ensure that the selected endpoint is terminal for that word.
Hence every target endpoint is covered. Conversely every generated
trace belongs to the permitted family because outside-F tetrahedra
remain idle and therefore survive. This proves exactness of the family.

### Proof: bit complexity and oracle accounting

Along a fixed-region execution there are at most i+2U moves, at most
n+U tetrahedra at any time, and at most 3i+5U assigned symbols. A new
diagonal cocycle value in a 2-3 replacement is a sum or signed difference
of two old edge values. A 3-2 move creates no new global edge values.
If initial absolute values are below 2^B, the largest absolute value
after u upward moves is below 2^(B+u), up to the harmless convention
for a sign bit. All arithmetic therefore uses B+U+O(1) bits.

Move enumeration, structural checks, production, and independent replay
are polynomial in these quantities for the given fixed-size local
replacement rules. Apply the endpoint oracle at the prescribed output
states. Its cost must be stated independently as above.

## Reverse-search generation of connected allowed sets

For a connected nonempty set A with root rho=min(A), define its canonical
parent by removing the largest-labelled x in A\{rho} such that
G[A\{x}] remains connected.

Such an x exists whenever |A|>1: take any spanning tree of G[A] and a
leaf other than rho. Removing that leaf leaves a spanning tree on the
remaining vertices, hence leaves the induced graph connected. The parent
has the same least vertex, is connected, and has size one smaller.
Iteration therefore reaches {rho}.

To enumerate the children of A, try every neighbour x outside A with
x>rho, form A' = A union {x}, and retain A' exactly when its canonical
parent is A. Every genuine child appears, because a newly added vertex
in a connected set must have a neighbour in the parent. Every child is
accepted by only its unique parent. After duplicate candidate neighbours
are removed, there are at most 4|A| candidates. Connectivity and parent
tests use polynomial work in r. Starting once at every singleton yields
every connected allowed region once.

For several components, generate components in increasing order of their
least vertices and require distinct selected components to have no face
adjacency. Bound the total selected size by r and the component count by
c. Every allowed F has exactly one decomposition into ordered connected
components and hence exactly one such generation path. Using the induced
graph after excluding selected vertices and their neighbours preserves
the degree-four bound and the canonical-parent existence argument.

## Consequences and precise limits

- For one connected allowed region and r+U=O(log n), the search is
  polynomial in n and the marking bit size B.
- For one connected allowed region and r+U=O(log^2 n), the search takes
  n^O(log n) poly(B) time.
- More generally, c=O(log n) and r+U=O(log^2 n) give the same
  quasi-polynomial bound.
- These are bounds for a precisely defined local reachability family.
  There is no proof that every unknot diagram, or every triangulation
  arising in a recognition hierarchy, admits a successful trace with
  these parameters.
- Total upward count, excess height, and number of upward bursts are
  different parameters. The proof controls the first one. It does not
  automatically preserve constraints on the other two.
- The predicate at endpoints must respect the transported marking and
  combinatorial isomorphism. A label-sensitive heuristic success rule is
  insufficient for the stated exact endpoint equivalence.
- The safe base in the counting bound is large. A practical speed-up
  requires measured pruning or partial-order exploration; it does not
  follow merely from the proof-device commitment enumeration.

## Sleep-set implementation inherits the same bound

This additional conclusion is valid under the following implementation
conditions:

1. There is one canonical action per eligible global edge/shared face;
   different choices of a root tetrahedron are not distinct action aliases.
2. An action identity uses the immutable identities of all consumed
   tetrahedron incarnations and their local selected ports. Output
   incarnation identities are exact structural terms determined by this
   action and the output local position. They are independent of execution
   order and global tetrahedron renumbering.
3. Independent actions have disjoint consumed supports, and each action
   and its residual after an independent move have the same identity.
4. The total-upward budget U and the fixed allowed region F are the only
   path constraints relevant to this reduction. Endpoint tests are
   isomorphism invariant with their markings.
5. The sleep-set DFS preserves at most one execution in each equivalence
   class under adjacent swaps of independent actions. No unsound extra
   state cache is combined with it.

First, sleep-set DFS has the property in (5). At a common prefix of two
distinct equivalent explored words, let a be the next action on the
earlier DFS branch. In the later equivalent word, a can be moved to the
front across every preceding action, each of which is independent of a.
After the earlier branch has been explored, a enters the sleep set for
the later branch. It remains there across that independent prefix and
so cannot be executed where the purported second representative needs
it. This is a contradiction. In the present incarnation system a
dependent move consumes a support tetrahedron, so it destroys that exact
action identity; a later newly born action cannot be confused with it.

Second, the number of trace equivalence classes is itself at most 11^N_i.
For any trace class, take its eventual-port/idle commitments and commute
ready events into the deterministic scheduler order as in the proof.
Record the resulting assigned symbols in the deterministic order in which
the executor requests them (the implementation chooses the least
unassigned immutable cell identity after executing any ready move),
padding to N_i with idle. This defines an injection from trace classes
to commitment words: if two classes gave the same word, the deterministic
executor would produce the same canonical trace from that word, while
both original traces are commutation-equivalent to that canonical trace.
They would therefore be the same class.

The executor need not assign all existing cells before firing a ready
move: whenever it requests a symbol, provide the intended eventual port
or idle symbol transported from the remaining target trace. The same
first-future-touch argument validates every early firing.

This argument includes all finite prefix traces. To encode a prefix,
declare all tetrahedra surviving that prefix idle; its deterministic
execution then stops precisely at its endpoint. Thus the number of
visited sleep-set nodes is bounded by the same 11^N_i, not only the
number of fully reduced leaves. Polynomial outgoing-move enumeration
and replay at each node preserve the stated singly exponential bound.

The choice of *exact structural* identities matters. A hash without an
exact equality check is not a mathematical identity guarantee. Likewise,
hash-cons table allocation numbers can be used as references only when
the represented structural terms, local output conventions, and residual
transport really agree across independently reordered histories.

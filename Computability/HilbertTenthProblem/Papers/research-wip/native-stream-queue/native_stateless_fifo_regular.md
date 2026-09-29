# Stateless equal-length FIFO rules give a regular raw-input language

For any fixed finite relation of paired read/append symbols, the native
equal-length queue with ordinary ternary input, existential zero padding,
and an all-zero endpoint accepts a regular language of ternary input
words. This remains true with one prescribed first rule and positive
stream requirements. The theorem applies to stateless selector/FIFO
compositions; it does not apply to a synchronized finite controller.

Thus increasing the number of stateless selector choices alone cannot
make the native FIFO component a universal representation of recursively
enumerable sets. No smaller complete arithmetic bound is established;
the complete bound remains 76.

## Exact machine and arithmetic scope

Fix a finite alphabet Sigma containing a zero symbol z, a delimiter #,
and the ordinary input symbols i(0), i(1), i(2), with z=i(0) and #!=z.
The native paired-trit instance is

    Sigma={0,1,2}^2, z=(0,0), #=(0,1), i(d)=(d,0).

Fix a finite set or list E of edges u->v in Sigma. At each step remove
the current first symbol u and append v along one chosen edge. There is
no separate control state. Nondeterminism and duplicate edges are allowed.
Optionally require the first step to use one particular edge e0.

For a positive ordinary integer x, choose ell with 3^ell>x and initialize
the queue with its ell low-to-high ternary digits, including any high
zeros, followed by #. Its length is m=ell+1. Accept if some finite run
ends with every symbol equal to z. The amount of padding and run length
are existential. The first-step condition is exactly what the selector
origin imposes when label zero has a fixed paired read/append row.

One may also require that specified finite flags occur along the run.
For example, flag each step according to which read and append trit
coordinates are nonzero. Requiring all four accumulated flags enforces
strict positivity of all four finite stream integers. If a containing
source derives streams as registers and permits zero, omit the corresponding
flag requirement. This distinction does not change the theorem.

The bounded native equations D_i=I_i+3^m*A_i are equivalent to precisely
these zero-reaching runs, by the scalar FIFO lemma in
[the native-stream proof](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md).
An exact selector predicate only fixes which edge appears at each common
time position. It adds no interaction between different queue tokens
unless further controller or routing equations are supplied.

## Independent token paths and exact run lengths

Write a proposed duration uniquely as

    t=h*m+p, 0<=p<m.

Label the original tokens by positions 0,...,m-1. A step changes the
symbol carried by a token and moves that token to the back. Token j
therefore takes exactly h+1 graph edges if j<p and exactly h edges
otherwise. These paths are independent: choosing a graph path for each
token and interleaving their successive edges in queue order produces
one valid run. Conversely, every run decomposes into these paths.

Consequently the queue ends at zero if and only if each initial token
has a path to z of its indicated length. With a prescribed first edge
e0:u0->v0, token zero must initially equal u0, must first take e0,
and then has a path from v0 to z of length h-1 if p=0, or h if p>0.
Any flag on e0 is included in its token's accumulated flags.

The delimiter starts at position m-1, which never belongs to the first
p tokens. It always takes h edges. Since #!=z, a successful run has
h>=1, including when a very short raw word was chosen. This also
recovers the native arithmetic consequence t>=ell+1.

## Only finitely many round relations are needed

Let G_n(u,v) be the set of flag masks obtainable on graph paths of exactly
n edges from u to v. A path mask is the bitwise OR of the flags on its
edges. G_0 is the identity relation with mask zero, and

    G_(n+1)(u,v) = union_w {a OR b: a in G_n(u,w), b in G_1(w,v)}.

These are finite matrices of finite sets. There are only finitely many
possible matrices. Iterating from G_0 until a matrix repeats therefore
computes a finite preperiod and a positive period. Equal matrices have
equal successors, so the resulting eventual periodicity is exact for
all future n. No number-theoretic effectiveness assumption is needed.

It follows that the triples

    (G_(h-1), G_h, G_(h+1)), h>=1,

range over an effectively computable finite set. After detecting the
first repetition, enumerating through one additional period after the
preperiod supplies every triple. This is an algorithm on a fixed finite
graph, not a free arithmetic instruction in a proposed certificate.

## A finite automaton recognizes the padded input words

Fix one of those triples and first consider p=0. Every token uses G_h;
the first token instead uses e0 followed by G_(h-1). A finite automaton
can read the initial queue word, choose an attainable mask for each
token path, and accumulate their OR in finite state. It checks the first
token separately and verifies the desired final mask.

For p>0, the first token uses e0 followed by G_h. Subsequent input
tokens initially use G_(h+1). The automaton nondeterministically chooses
one cut, after which tokens use G_h. It must make that cut before
reading the final delimiter; this expresses 1<=p<m exactly. All local
choices and accumulated masks are finite. This recognizes precisely the
successful initial words for the chosen triple and cut case.

Intersect with the regular format of at least one ordinary digit followed
by exactly one delimiter, and take the finite union over triples and the
two cut cases. The resulting regular language K consists exactly of
accepted padded initial words. In the version without a prescribed first
edge, simply use the indicated G_h or G_(h+1) relation at token zero.

Finally a canonical positive ternary word w (low-to-high order, final
digit nonzero) represents an accepted x exactly when

    w 0^k # is in K for some k>=0.

This is an effective regular-language operation: in an automaton for K,
mark as accepting every state from which a sequence of zero symbols
followed by a delimiter can reach a previous accepting state. Compute
those states by finite graph reachability. Then restrict the input to
canonical positive ternary words. This removes padding and proves the
regularity theorem for ordinary x, with an explicit decision procedure.

## Consequences and limits

The result applies to any fixed finite collection of stateless paired
rows, not only the three labels of the current 54-operation selector
module. Its proof includes nondeterministic rules, arbitrary permitted
history lengths, all positive padding lengths, the fixed origin rule,
and optional stream positivity. For every such graph the accepted set
of ordinary integers is decidable. Since some recursively enumerable
sets are undecidable, this family cannot be a universal representation
scheme for all recursively enumerable sets.

A finite controller changes the graph edge available to one token based
on other previously processed tokens. The independent-path decomposition
then fails. Variable-length rewriting, updating neighboring tokens, extra
equations coupling distant selector positions, and a redesigned transport
are also outside this theorem. In particular, the existing universal
delayed loader has a controller and is not refuted by this result.

## Evidence

The companion [checker](native_stateless_fifo_regular.py) compares direct
queue execution with the exact round decomposition on all ordered
three-edge graphs over a three-symbol alphabet, including duplicate edges.
It retains nonzero-read and nonzero-append flags, exercises short and
long durations, and compares iterated graph powers with their computed
eventual period. The three-symbol fixtures are finite checks of the
general graph lemma, not full paired-trit compiler witnesses.

The regular-language construction above is a mathematical proof. Finite
checks do not establish regularity for arbitrary graphs by themselves.
An independent full scoped proof/source review and fresh default replay
pass, with no findings. The receipt records 729 graphs, 34,992 direct
queue/round comparisons and 5,424 repeated-power checks. Run the checker
without arguments to compare its [saved receipt](native_stateless_fifo_regular.json).

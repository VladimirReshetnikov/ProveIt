# Exact finite-window memory of a filtered carry controller

This note characterizes the labelled language of the fixed carry graph
in the [general75 architecture](native_dualrail_fifo67.md). It does not
remove the FIFO relation, construct a universal compiler, or decide the
ordinary-input language of the coupled system. Local window constraints
can still be useful in a computational space-time encoding.

## 1. A long label word selects one path; it does not merge states

Fix integer coefficients c0,...,c3, offset h, and endpoints cs,cf. A
label ell is a four-bit tuple. Write

    g(ell)=h+sum_i ci*ell_i,
    3 k_(j+1)=k_j+g(ell_j).

Set

    B=max(abs(cs),ceil((abs(h)+sum_i abs(ci))/2)),
    S={-B,...,B}.

This interval contains every carry reachable from cs. More strongly,
every integral transition starting in S stays in S: abs(g)<=2B and
abs(k+g)/3<=B. If cf is outside S the accepted language is empty.
All coefficients and B are fixed independently of input and length.

For a word v=(ell_0,...,ell_(t-1)), put

    T(v)=sum_(j=0)^(t-1) g(ell_j)*3^j.

Telescoping gives the exact affine map

    3^t*k_t=k_0+T(v).                                  (1)

Conversely, if k_0 in S makes k_0+T(v) divisible by3^t, then every
prefix numerator is divisible by its corresponding power of3. The
resulting intermediate carries are integral and stay in S. Thus (1)
also gives an exact path test, rather than only a necessary condition.

Choose any n>=1 with3^n>2B. If v has at least n labels and has two
paths in S, subtract (1). Their initial carries differ by a multiple
of3^t while their difference has absolute value at most2B. Therefore
the initial carries are equal, and so are the entire paths. This is
stronger than an eventual merging property. A fixed label word always
acts injectively; distinct initial states cannot merge at any length.
For sufficiently long words, at most one initial state is admissible.

There is a direct residue formula. For t>=n, let

    start(v)=-B+((-T(v)+B) mod3^t),

where the remainder is in[0,3^t). The word is feasible in S exactly
when start(v)<=B, and then its unique terminal carry is
(start(v)+T(v))/3^t. This supplies effective finite tables below without
searching over unbounded states.

## 2. Exact windows, including both boundaries and short words

Precompute these finite sets over the sixteen-label alphabet:

- P: length-n words whose unique path starts at cs;
- F: length-n words whose unique path ends at cf;
- V: length-(n+1) words having a path anywhere in S;
- E: all accepted words of lengths strictly below n, tested directly.

For any word w of length at least n, the carry accepts w from cs to cf
if and only if its first n labels belong to P, its last n labels belong
to F, and every consecutive (n+1)-label window belongs to V. Words
shorter than n are accepted exactly when they belong to E. Empty words
can be included in E for this language theorem; the FIFO source itself
requires a positive run length.

Necessity follows by restricting an actual path. For sufficiency, if
the word has length n, the two boundary tests refer to the same unique
path. Otherwise consecutive allowed windows overlap in n labels. Each
overlap has at most one entire path, so the window paths agree on every
overlapping state and edge. They join to a path on the whole word.
The first and last n-label paths then force the two prescribed endpoints.

This is an exact finite-window presentation, often called strict local
testability, with explicitly paid attention to its prefix and suffix.
The tables are computable from the fixed program numerals. They are not
extra arithmetic constraints to be charged to the75 source: the source's
single weighted equality already enforces this exact carry language.
Nor can arbitrary chosen tables be substituted for these particular
tables without a separate synthesis proof.

The first-append condition in the65 FIFO can simply restrict the first
label of P (or of E for short words). This does not change the argument.
The FIFO itself links positions a variable distance apart and remains an
additional condition; the finite-window theorem does not eliminate it.

## 3. Concrete criteria for a proposed finite controller

A proposed implementation by distinct integer state codes must satisfy
all of the following constraints on its full four-bit edge labels.

First, transitions with the same label cannot merge different states:
the predecessor is uniquely 3k_next-g(ell). A reset operation that maps
two distinct coded states to one state with the same complete label
therefore cannot be implemented directly. Different append or rail bits
may distinguish two labels even when their scalar read symbols agree.

Second, no sufficiently long word can be possible from two different
states. A useful coefficient-independent test is the off-diagonal pair
graph of a proposed deterministic labelled controller. Its vertices are
pairs of distinct states; its edges follow the same full label from
both components. Direct affine coding excludes edges into the diagonal
by injectivity, and excludes any cycle in this pair graph: repeating a
cycle would give arbitrarily long common label words from distinct
states. This is a necessary graph test, not sufficient affine synthesis.

Third, a fixed repeated label block cannot implement a hidden modular
counter. For any nonempty block u, its partial state map has form

    f_u(k)=(k+T(u))/3^length(u).

Its only possible periodic points are fixed points. More sharply, for
any states s,t in S, if u^p and u^q both take s to t with0<=p<q,
then s=t, the u-path is a loop there, and every u^j takes s to t for
j>=0. To see this, t is periodic under f_u^(q-p), hence is its unique
fixed point; injectivity of f_u^p then forces s=t. The intermediate
u-path at that fixed point exists because one of the positive repetitions
exists. In particular an unannotated unary even-length counter, or an
unannotated threshold that accepts precisely u^j for j>=2, cannot be
the exact carry language. Explicit phase labels, boundary markers, or
constraints from the FIFO change the question and are not excluded.

Fourth, the graph sees a label only through g(ell). Labels with equal
weighted sums have identical carry edges at every state. They can still
have different FIFO read/append meanings. A compiler must account for
every such alternative in the whole coupled system; merely satisfying
the desired edges proves no exclusion of unintended paths.

These facts suggest a precise use for serialization: expose enough
control information in bounded label windows, then solve the affine
constraints and check the whole induced labelled graph. For a proposed
length-l transition block v from state s to state t, the exact constraint
is 3^l*code(t)-code(s)=T(v), with the same four weights and offset shared
across every block. State refinement or serialized phase information may
meet the window criterion, but no construction achieving universality
with the four available rails follows from this criterion alone.

## 4. Evidence and scope

The [checker](input_bridge_carry_memory.py) enumerates coefficients in
{-1,0,1}, offsets in{-1,0,1}, and starts in{-2,...,2}. It tests unique
bounded models after grouping identical weighted alphabets. Weighted
letters are equivalence classes of the sixteen Boolean labels; equal
weight classes are checked explicitly. For each model it compares the
direct transition graph against the residue and window reconstructions,
including all boundary state pairs and short words. It also tests
injectivity and the repeated-block endpoint consequence.

These are focused finite checks of the universal proofs above. They do
not test a universal FIFO compiler or arbitrary local relation synthesis.
Default execution compares the [saved receipt](input_bridge_carry_memory.json).
The complete universal bound remains76. Independent proof/source/default
review passed, including the boundary cases and the scoped compiler criteria.

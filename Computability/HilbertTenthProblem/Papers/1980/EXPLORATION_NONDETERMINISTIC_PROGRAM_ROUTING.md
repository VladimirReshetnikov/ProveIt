# A fixed nondeterministic graph router in 68 operations

A column-count marker in the constant program table extends the absorbed
68-operation deterministic router to an arbitrary fixed finite directed
graph. Each time row still contains exactly one state, but that state may
choose any allowed successor. The complete count remains **68 operations:
38 multiplications and 30 additions/subtractions**, with one positive
parameter q, 23 positive unknowns, and 16 equations.

The exact relation is existence of a path of length t from a fixed initial
state to a fixed final state, with q=W^t and t>=1. This fixed finite-graph
predicate is decidable. No counter condition, zero test, variable-width
program composition, or universal-machine bound is claimed. The projection
interface in Section 7 explicitly charges the additional operations for
linking already typed counter flags.

The complete source checker and finite receipt are
`../verification/explore_nondeterministic_program_routing.py/.json`.
The frozen deterministic70 and absorbed deterministic68/permutation66
artifacts remain unchanged.

## 1. Fixed constants, edge terms, and the count marker

Let a fixed directed graph have m>=2 states, with no self-loops and no
parallel copies of an edge. Denote its edge set by E. Self-loops can be
removed by the usual phase split: replace state i by (i,epsilon), and
replace edge i->j by (i,epsilon)->(j,1-epsilon). The endpoint phase remains
part of the fixed endpoint specification; this transformation does not
silently existentially choose an endpoint phase.

Choose a fixed integer l>=2 such that

    3^l>m, l-1=m modulo 2.

Set

    a_i=l*3^i, d=max_i a_i,
    S=sum_i 3^(a_i), g=3^d,
    K=sum_((i,j) in E) 3^(d+a_j-a_i)+sum_i 3^(d-a_i),
    Z=sum_(h=1)^(l-1) 3^(d+h).                         (1)

Fix initial and final states i0,i1, and set I=3^(a_i0), F=3^(a_i1).
Choose a fixed even B and W=3^B so large that

    W>max(KS,gS,2S+1,Z).                              (2)

Every quantity in (1),(2) is a fixed numeral. Its compilation may depend
on the graph, but no variable exponentiation is a free operation in the
certificate. Products involving these numerals are counted below.

The set of a_i is Sidon: equality of two sums of two of its elements
determines the same unordered pair. Consequently two different loop-free
edges have different differences a_j-a_i. Marker exponents d-a_i are also
distinct. An equality between an edge exponent and a marker exponent
would require a_i=a_j+a_h for some indices. This is impossible for the
positive powers l*3^i, including repeated indices. Thus every exponent of
K is nonnegative and distinct, and K is a Boolean ternary numeral.

Consider any source subset U, with word c_U=sum_(i in U)3^(a_i). Before
normalization, the coefficient of K(T)c_U(T) at the marker position d is
exactly |U|. Only the matching marker term d-a_i contributes: an edge
term reaching d would again require one power of three to equal a sum of
two positive powers.

At an ordinary target d+a_j, the raw coefficient is the number of edges
from U to j. The marker terms cannot reach this target. For an edge
(h,j') to contribute from source i, the equation is

    a_i+a_j'=a_h+a_j.

The Sidon alternatives give h=i,j'=j, or i=j,j'=h. The second would be a
self-loop and is excluded.

All product exponents are multiples of l. Every raw coefficient is at
most m: for a fixed exponent and a fixed source monomial, there is at
most one matching term of K, since K has distinct exponents. Since
3^l>m, there is no carry between adjacent base-3^l blocks. In particular
the complete normalized block of length l starting at d is the ordinary
ternary representation of |U|. This remains valid when U has several
states. By (2), Kc_U<W, so multiplication also creates no carry between
time rows.

## 2. Complete positive source and arithmetic count

The positive parameter is q. Supply positive H,C,V,TestC,TestV,alpha and
the seventeen positive variables of the retained 43-operation kernel in
`EXPLORATION_BASE_THREE_PELL_KERNEL.md`. Impose

    q=(W-1)H+1,
    TestC=C+[((W-1)/2)-S]H,
    TestV=V+ZH,
    (WK-g)C+gI=(gF)q+WV,
    TestC+TestV+alpha=q.                              (3)

All coefficients displayed here are fixed numerals. The first complement
coefficient is strictly positive by (2). The five equations cost thirteen
operations: two for geometry, two for each support equation, five for
routing, and two for the shared bound.

Pack all four fields

    P0=C+qV+q^2 TestC+q^3 TestV.                      (4)

This takes six Horner operations. Append the complete 49-operation
lower-half ternary mask and Pell component with

    L=q^4, D0=9L, r=D0-3P0-1.                        (5)

The latter component has the eleven equations and full positive converse
in `EXPLORATION_BASE_THREE_PELL_KERNEL.md`; none is dropped or weakened.
Thus the total is 13+6+49=68. Relative to absorbed deterministic68, the
only source change is replacing the fixed junk-forbidden coefficient gS
by Z. The table K is also a different fixed numeral. Both changes have
zero construction cost under the fixed-numeral convention, while the
products with those numerals remain charged.

The checker restates and verifies all sixteen expanded source residuals
against the complete list of 68 primitive operations, including the
retained acyclic correction of the auxiliary Pell norm. The exact
histogram is 38M+30A. No supplied Rep is restored: below Rep means the
mathematical value (q-1)/2, as in the already verified fixed-complement
absorption.

## 3. Bounds, power recovery, and support

Positivity in (3) gives q>=W and

    0<C<TestC<q, 0<V<TestV<q.                         (6)

Thus 0<P0<q^4 before any digit interpretation. The complete mask's
soundness implication recovers q as a power of three and all four fields
C,V,TestC,TestV as Boolean ternary words below q. This implication does
not require r to have a prescribed parity.

Since W=3^B and W-1 divides q-1, q=W^t for some integer t>=1. Therefore
H is the base-W repunit and Rep is the full ternary repunit below q.
The equation TestC=C+(Rep-SH) is now a sum of two Boolean words. Such a
sum has digits at most two and no carries. TestC being Boolean therefore
forces C to be supported on SH. Its row j encodes a subset U_j of the
fixed state positions, possibly empty or initially with several states.

Likewise ZH is Boolean: its nonzero digits are the positions d+1 through
d+l-1 within each row. TestV=V+ZH, with V and TestV Boolean, forces V to
be zero at all these forbidden positions. This proof does not assume any
head count or choose a successor in advance.

## 4. Recover the mathematical next-state word

Reduce the routing equation modulo W. Since q is a multiple of W and g
divides W, the first row c0 of C satisfies c0=I modulo W/g. Both numbers
are at most S, and gS<W by (2). Therefore c0=I as integers.

Define the mathematical quantity

    Next=(C-I+qF)/W.

It is a positive integer made from the remaining rows of C followed by
the fixed singleton final row F. It is Boolean, supported on SH, and
below q. Rearranging the routing equation gives

    KC=g Next+V.                                    (7)

There is no certificate division in this argument; the divisibility is
a deduction from the already recovered first row. Because each row of
g Next is bounded by gS<W, shifting by g creates no carry between rows.
Both g Next and V are Boolean, so their sum has digits at most two and
has no ternary carries anywhere. The rows of KC are also separate by
KS<W. Equation (7) may therefore be read row by row.

## 5. The marker forces exactly one state and one chosen edge

At the marker block d,...,d+l-1, g Next has no support: its first possible
state output is d+a_0=d+l. V has zero digits at all marker positions
except possibly d. Its digit at d is Boolean. Consequently the marker
block of the right side of (7) is zero or one.

Section 1 identifies the same normalized block on the left as |U_j|.
It follows that every row of C contains at most one state. The argument
does not infer this from the marker's low ternary digit alone: every
higher digit in its full length-l block is explicitly forbidden, so a
count such as three cannot masquerade as one through a carry.

If any source row were empty, its KC row would be zero. Nonnegativity
in (7) would make the corresponding Next row zero. Every later source
row would then be empty by induction, contradicting the fixed singleton
final row. Thus every source row, and every Next row, is a singleton.

For a singleton source i, its product K3^(a_i) is a shift of the Boolean
numeral K. At the target d+a_j its digit is one precisely when (i,j) is
an allowed edge. A singleton Next at j contributes one there on the
right of (7). Hence (i,j) must be an allowed edge. Unchosen edge outputs
remain as Boolean junk in V. Unlike the deterministic predecessor, they
are not forbidden. We have recovered an actual path

    i0 -> i_1 -> ... -> i_t=i1

of length t. No external promise of one-hot state rows or allowed branch
choices was used.

## 6. Positive converse, including the fixed-sign kernel parity

Conversely let such a path be given. Set q=W^t and take its source and
successor singleton rows as C and Next. Put

    H=(q-1)/(W-1), Rep=(q-1)/2,
    V=KC-g Next,
    TestC=C+Rep-SH, TestV=V+ZH,
    alpha=q-TestC-TestV.                             (8)

For each source row, the chosen edge output occurs with digit one and
is removed without borrowing. The resulting V is Boolean. Its marker
digit at d is still one, so V is strictly positive, even for a graph
whose traversed state has only one outgoing edge. All other product
terms lie on the l grid, so V avoids every forbidden digit of Z. Thus
both Test fields are Boolean and positive, at most Rep, and alpha>=1.
All other outer witnesses are positive and every equation (3) holds.

The parity needed by the retained fixed-sign positive Pell converse is
automatic. The support equations give

    C+V+TestC+TestV=2(C+V)+Rep+(Z-S)H.

Rep is even because the fixed exponent B is even. A ternary numeral has
the parity of its digit sum, so Z-S is even because Z has l-1 one digits,
S has m one digits, and l-1=m modulo two. The sum of the four packed
fields is therefore even. Since q is odd, P0 is even, and (5) makes r
even. The existing full positive mask and Pell converse supplies all
seventeen remaining variables. This completes all 23 positive unknowns;
no parity field or parity equation has been added.

## 7. Counter-output projections and the variable-frame boundary

The construction removes the need for a separate masked branch-selection
word merely to choose an allowed edge. It does not make the chosen branch
depend on a counter value. The following describes a separately charged
projection interface, not an additional complete 68-operation theorem.

Suppose a counter component already supplies a raw word Q typed as a
Boolean subset of H. Mark a fixed subset of program states as emitting
that flag. Take the fresh coordinate b=l*3^m from the same extended
Sidon sequence, and enlarge d and the fixed frame as needed. For several
flags use distinct later coordinates from that sequence. This preserves
both the l grid and the marker/target separation. Add to K the terms

    3^(d+b-a_i) for the states i that emit the flag.

Add target d+b to V's forbidden mask. The desired routing identity is

    KC=g Next+hQ+V, h=3^(d+b),

or, after the same time elimination,

    (WK-g)C+gI=(gF)q+W(V+hQ).                       (9)

The fresh Sidon coordinate separates the flag target from ordinary
successor targets and the count marker. If Q is already typed, the
right side has no carry: g Next and hQ have disjoint Boolean support,
and adding Boolean V gives digits at most two. The forbidden flag digit
then forces Q to equal the emitted label in every row. Marker recovery
is unchanged. The enlarged forbidden-mask weight may be accommodated by
choosing l's parity accordingly.

Relative to the existing routing calculation, hQ and V+hQ cost **one
multiplication and one addition**. Several already typed raw flags add
two operations each, sharing the outer product by W. If the counter
supplies a native flag FQ=J+Q and does not already compute Q, extracting
Q=FQ-J costs another subtraction. These projection counts exclude any
new field masking, typing, range equations, and global scale changes.
In particular a raw flag that vanishes everywhere need not become a new
strictly positive supplied unknown; it may be a computed intermediate.

The fixed-frame cost also does not transfer unchanged to a variable
counter frame R. Constructing RK-g costs two operations. The source
support becomes C+J=SH+TestC when using the counter's shared native
repunit, and costs three operations instead of two. Geometry may be
shared, so the five-equation outer interface then costs fourteen
operations before additional flags, packing, or new bounds. The proof
still requires R>max(KS,gS,2S+1,Z). This inequality must be derived from
paid equations. For example, with a fixed sufficiently large power of
three Rmin, imposing R=Rmin*z with positive z costs one multiplication
and is compatible with widening a counter frame. This is a counted
possible bound, not an assertion that an existing counter already has it.

Zero-event flags still require an exact test on the selected counter
rows. Linking a flag to a fixed program label proves only the label's
consistency, not that the counter is zero. Therefore the 68-operation component and
these incremental projection counts imply no universal-machine total.

## 8. Exact evidence

The checker verifies the complete 68-operation arithmetic and all 16 equations.
Its finite phase examines all 68 loop-free directed graphs on two and
three states, including empty graphs and states with no successors. It
checks 2,096 normalized marker/target identities on arbitrary source
subsets, 632 canonical paths of lengths one through three, and 37,120
arbitrary two-row subset tuples with every initial/final state. The
complete masked relation accepts 194 of those tuples, all actual paths.
Acceptance uses the independent factorial valuation, without a one-head
or chosen-edge filter. These finite checks supplement the general proof;
no enormous positive Pell tuple is numerically instantiated.

# Positive bilinear outcome certificates for finite lattice-game boards

A fixed finite acyclic game graph admits one bilinear comparison per
nonterminal position, with **no separate Boolean equations**. Positive
coordinates force every outcome bit to be Boolean. A sum of squares
then gives a complete degree-four polynomial for the specified finite
graph and target outcome. Its size grows with the graph; it is not a
fixed-variable universal polynomial.

For N vertices, h nonterminals and E directed edges, the literal
certificate costs **E+3h=2hM+(E+h)A**, with N+h positive witnesses.
Requiring one target outcome adds a comparison but no certificate gate.
The resulting single polynomial costs **E+3h+3N+2**, with N+1 comparisons.
The five-vertex example is19 certificate /36 polynomial operations,
with9 witnesses and6 comparisons. This local method does not improve
the complete [301-operation alternative](neary_woods_universal_joint_and_arithmetic.md)
or the [87-operation universal polynomial](complete75_normalized_strong87.md).

## 1. Primary-source universality and its actual quantifiers

Alex Fink's [*Lattice games without rational strategies*](https://arxiv.org/pdf/1106.1883),
Theorem1.2 and Corollary1.3, gives universal computation in lattice
games on N³. One version fixes the moves and encodes input in finitely
many defeated positions; another changes the moves. The undecidable
query asks whether some position (mi+a,mj+b,1), with i,j unbounded,
is a P-position. It is not the outcome query for one specified finite
position. P means losing for the player about to move; it is the NOR
of the options' P-bits.

Example2.5 supplies an explicit28-move game with no rational strategy,
not a numerical universal game table. The checker transcribes that
example and checks its stated binomial-parity output pattern. Its role
here is an actual lattice-rule fixture, not a universal arithmetic bound.

The repository's existing local Boolean, counter, cellular-automaton,
tag and matrix components do not supply this positive divisibility
encoding of a whole acyclic option graph.

## 2. One bilinear equation forces the outcome bit

Let G be a finite directed graph, with an edge v→j for every legal
option j of v. Let r_v be its outdegree and d=max(2,max_v r_v). Fix

    D=lcm(1,2,...,d).

For each vertex supply a positive integer u_v. For each nonterminal
vertex also supply a positive integer w_v. Write

    S_v=sum_{v→j}(u_j-1).

At a nonterminal impose

    S_v*w_v+D*u_v=2D.                                  (1)

At a terminal impose u_v=2, with no w_v needed. All constants here
are determined by the finite graph or a fixed upper bound on its
outdegrees.

Every u_j is positive, so S_v>=0 before any equation. Equation(1)
therefore implies u_v<=2. Together with positivity this forces
u_v∈{1,2}; terminal comparisons give the same conclusion. This
argument applies to all vertices simultaneously and does not assume
that their options were already typed.

Put p_v=u_v-1. All p_v are now Boolean. If every option has p_j=0,
then S_v=0 and(1) forces p_v=1. If at least one option has p_j=1,
then S_v>0. Positivity of w_v excludes u_v=2, so p_v=0 and

    w_v=D/S_v.                                         (2)

Conversely, suppose the Boolean labels obey NOR at every vertex.
When S_v>0, it lies in{1,...,r_v}, so it divides D and(2) is a positive
integer. When S_v=0, any positive w_v works. Terminals have p_v=1.
Thus(1) and the terminal comparisons have precisely the Boolean NOR
labelings as their positive projection. The outcome labels are not
supplied as an unproved Boolean promise.

The multiple D is essential to this converse. With two terminal
P-options, the parent's sum is2 and its correct label is p=0.
Replacing D by1 would require2w=1 and lose this valid outcome.
Multiplication by D is an actual paid gate below.

For an **acyclic** graph, induction from terminals gives exactly one
NOR labeling: the normal-play outcome at every vertex. Therefore a
target comparison u_t=b+1, for b∈{0,1}, has positive witnesses exactly
when the true target P-bit is b. For a cyclic graph the algebra would
instead describe its Boolean NOR fixed points, which can be absent
or nonunique; that is not a theorem about terminating normal play.
The source accepts only a supplied topological ordering, with every
option index strictly smaller than its parent index.

## 3. Literal graph compiler and exact counts

The [source](lattice_game_positive_nor.py) builds each nonterminal row
by summing its r_v option hats, subtracting r_v once, multiplying by
w_v, multiplying u_v by D, and adding those products. It compares the
result with the fixed numeral2D. The row therefore costs

    2M+(r_v+1)A = r_v+3 operations.

Both fixed numerals D and2D are compiler data; the multiplication
D*u_v is counted. No multiplication is discarded when D happens to
equal2. A terminal comparison u_v=2 requires no certificate gate.

Let c=N+epsilon, where epsilon is1 if the target comparison is
present and0 otherwise. Even when a target comparison repeats a
terminal comparison, the displayed compiler retains it; no minimality
claim is made. Summing the rows gives

| Item | Exact literal count |
|---|---:|
| Certificate multiplications |2h|
| Certificate additions/subtractions |E+h|
| Comparisons |c|
| Positive witnesses |N+h|
| SOS multiplications |2h+c|
| SOS additions/subtractions |E+h+2c-1|
| SOS total |E+3h+3c-1|

Each comparison is converted to one residual and one square, and
the c squares use c-1 further additions. If h>0 the degree is exactly4:
the nonterminal residual's quadratic part is

    w_v*sum_{v→j}u_j.

Under the specialization assigning every variable the same indeterminate
z plus any fixed offset, the degree-four coefficient of the SOS is
sum_v r_v²>0. This also verifies that the upper bound obtained from
the source DAG is attained. With no edges the degree is exactly2.

For example, use option lists

    [], [0], [0,1], [1,2], [2,3]

and require vertex4 to be N. The unique P-bits are(1,0,0,1,0).
Here N=5,h=4,E=7,D=2: the certificate is19=8M+11A,
and its polynomial is36=14M+22A, with9 witnesses and6 comparisons.
This is an explicit complete finite-graph polynomial, not an
arithmetic charge for an entire universal lattice game.

## 4. Predecessor-closed finite boards and two false shortcuts

Consider a fixed finite move set Gamma⊂Z^k. A move from a legal
position p subtracts gamma∈Gamma when p-gamma is another legal
position in N^k outside a fixed finite excluded set F. Assume fixed
positive integer weights a_1,...,a_k satisfy

    a·gamma>0       for every gamma∈Gamma.               (3)

This condition makes the rank a·p decrease strictly along every move.
For any integer R>=0, let

    V_R={p∈N^k\F : a·p<=R}.                             (4)

This set is finite and closed under every legal option of its
vertices. Indeed, a legal option is nonnegative, is not in F, and
has strictly smaller rank. Sorting V_R by rank supplies the required
topological ordering. The complete finite graph in Section2 therefore
computes the actual infinite-board outcome of every position in V_R.
Increasing R cannot alter those outcomes. One may fix
D=lcm(1,...,max(2,|Gamma|)) for every radius, rather than change D
when the realized outdegrees change.

The positive weights allow negative coordinates in individual move
vectors. No coordinatewise-decrease promise is used. For instance,
(2,-1) and(-1,2) both decrease rank with weights(1,1).
The literal28-move fixture satisfies(3) with weights(1,1,3).

Closure and inclusion of **every legal option** are necessary. In the
one-heap subtraction-by1 game, position1 is N because it can move to
terminal0. Truncating the graph to the singleton{1} makes it terminal
and falsely labels it P.

Even keeping all vertices does not license selecting just one path.
For subtraction moves{1,2}, the graph on{0,1,2} has option lists

    [], [0], [0,1],

and P-bits(1,0,0). Deleting the edge2→0 leaves a path with P-bits
(1,0,1). Its purported positive target-P certificate with D=2 is

    (u0,u1,u2)=(2,1,2),       (w1,w2)=(2,1).

Every row of that reduced graph and its target comparison vanishes.
Restoring the omitted option forces w2=0, contradicting positivity.
Thus a guessed option path can give a complete zero of the wrong
finite-graph polynomial; it cannot replace the full option relation.

## 5. The remaining universal-input obstruction

For fixed moves, weights and excluded set, the outcome of a supplied
finite position p is decidable: enumerate V_{a·p} and evaluate its
finite acyclic graph. Consequently, for every total computable map
x↦p(x), the language

    {x : p(x) is a P-position}

is decidable. In particular, neither an affine nor a polynomial
ordinary-input loader into one position can by itself represent an
undecidable recursively enumerable set. This is a semantic obstruction
to that specific direct interface, not a restriction on arbitrary
Diophantine encodings or on lattice-game universality.

The primary theorem instead retains unbounded existential position
coordinates. An eventual arithmetic representation must pay for that
position, its complete finite dependency region, all legal options,
the source's varying-input format and the queried output locus. The
present compiler's variable count and circuit length grow with that
region. Quantifying a radius does not turn this family of differently
sized polynomials into one fixed polynomial. A uniform packing or a
different bounded-variable history theorem is still required.

The concrete advantage is the positive row(1): it types every local
outcome without a separate Boolean/Pell predicate and uses a fixed
multiple for all bounded outdegrees. The current297 and87 constructions
already solve different, complete ordinary-input contracts. No smaller
universal operation count follows here.

## 6. Exact checks and reproducibility

The [receipt](lattice_game_positive_nor.json) records:

- 512 literal full-source residual/SOS identities,256 signed, and32
  exact leading-coefficient checks;
- All1,099 ordered DAGs on at most five vertices, with254,253 positive
  output assignments from{1,2,3}, plus each genuine extension and each
  opposite-target check;
- 18 full predecessor-closed boards, totaling1,341 vertices and3,654
  edges, with both ordinary and excluded-position cases and invariance
  under increasing the rank bound;
- The actual28-move fixture on4,109 positions through rank39,28
  binomial-parity queries, and a full positive source zero on its
  185-position rank12 board;
- The explicit omitted-position and omitted-option counterexamples.

The rank12 fixture has366 positive witnesses and2,803 polynomial
operations. Its size illustrates the uncompressed board cost, not a
new universal bound. No native Pell theorem or giant Pell coordinates
are required by this finite-graph certificate.

```sh
python3 lattice_game_positive_nor.py
```

Review status: author writer and fresh default pass. Native's independent
full proof/source review and fresh default pass with no findings, including
direct checks of the primary theorem, corollary and all28 example moves.
His additional512 signed complete-source identities on64 new DAGs pass;
a separate memoized legal-move recursion agrees on96 board queries,
covering1,424 evaluated positions. All four local links resolve.

Root full proof/source review and a fresh default replay also pass without
findings. Root checked the primary Theorem1.2 and Corollary1.3 against the
stated scope: universality uses unbounded position queries, and the
explicit28-move example is not asserted to be a universal ruleset.

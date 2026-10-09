# Proof audit and failure boundaries

This is an internal mathematical audit of the delivered arguments. It is not
external peer review or a proof-assistant certificate.

## Finite algebra

**Graph convention.** A vertex is a coarse block on one side. An edge is one
labelled actual arc; parallel edges are never deduplicated. Isolated vertices
cannot occur in a nonempty partition envelope because blocks are nonempty.
The two sides remain distinct even when the partition arrays coincide.

**Disconnected envelope.** Refinement only splits vertices, and cannot connect
separate components of the coarse graph. Every restricted completion entry is
zero. The `2^lambda` statement is asserted only for connected envelopes.

**Cycle dimension.** Connectedness gives `lambda = r - (s+t) + 1`. This number
is nonnegative, and a spanning tree leaves exactly `lambda` chord edges. Each
vertex has a spanning-tree incident edge when `r>=1`, so the core block in the
sharpness construction never becomes empty.

**Split constraints.** Each split vertex imposes even incidence in each new
block. One equation per old vertex is redundant because the old cycle already
has even total incidence there. All remaining equations, including dependent
ones, are retained. The cycle-space kernel identity does not assume they are
independent.

**Determinants.** A disk-compatible pair has complementary grades `j+k=lambda`.
Then the stacked constraint matrix is square, and a zero cycle space means its
determinant is one over F2. Edge and vertex counts make acyclicity equivalent to
a connected tree only in this complementary-grade case. Other grades are
explicitly assigned compatibility zero, not tested by a rectangular determinant.

**Zero rows.** `rank(A_p)=j-c(p join rho)+1`. If `p join rho` is disconnected,
all maximal minors vanish. If it is connected, the `j` rows are independent,
so at least one maximal minor is nonzero. This is an exact test, not a heuristic.

**Empty cases.** At cycle rank zero the feature space is one-dimensional, the
empty determinant is one, and only unsplit grade zero can survive. At one arc,
the connected envelope is a single edge and the theorem has this same meaning.
The prototype handles empty candidate/option/cap lists; interfaces themselves
remain nonempty until the terminal cap.

**Sharpness.** Detaching a chosen chord on the left contributes precisely that
chord's coordinate unit row in a fundamental-cycle basis. Right detachments
work independently. Complementary subsets give a spanning tree with chord
stubs as leaves. Their compatibility submatrix is a permutation matrix of
order `2^lambda`; fixed grades select its binomial blocks.

**Coordinate choice.** An invertible cycle basis change acts invertibly on each
exterior grade. Changing which split-block equation is omitted performs an
invertible row transformation. Over F2 its determinant is one. Identities among
feature rows are therefore preserved even when the checker uses other choices.

## Optimization and continuation

**Actual witnesses.** Linear combinations are identities among observations,
not instructions to XOR physical surfaces. The output is a subset of actual
input candidates. Pairing a successful input row with a cap forces at least one
no-more-expensive retained summand to succeed.

**Cost contract.** Finiteness permits negative costs. Sorting is by actual signed
integer cost; magnitude is not treated as a unit-cost machine word. The retained
subset preserves minimum scalar costs and existence, not counts or all optima.
Sectors are reduced separately, and costs and sectors combine as specified.

**Whole contexts, not only the next move.** For a successful final disk, everything
outside a partial object is an admissible disk-union cap. A replacement must
admit that same outside geometry and rules. Intermediate cycles or sealed
components cannot occur in a successful replacement because defect is
monotone and later attachments cannot reconnect an arc-free component.

**Envelope compiler.** The compiler joins the old coarse connectivity with all
explicit patch options and then restricts labels. This may combine mutually
exclusive options, so it is conservative rather than exact. Refinement induction
proves containment. No suffix assembly enumeration is charged as free.

**Unsafe operations.** Narrowing future caps is safe for an already valid family.
Widening is not: at two arcs, a formerly impossible candidate may become the
only successful one. Filtering the past source after reduction is also not
licensed unless replacements survive or reduction is redone on the eligible
original family. Hidden same-component guards can defeat substitution.

## Topology and global complexity

**Topology.** Every surface component has nonempty boundary. Finite disjoint
proper closed arcs leave free boundary gaps. Inclusion–exclusion subtracts one
per interval, and the quotient component graph counts connected components.
The classification formula makes every input/output defect nonnegative.
Whole-circle gluing, capping, and compression surgery need other theorems.

**Ambient geometry.** Abstract polygon gluing proves an abstract surface is a
disk. It does not prove that the disk embeds in a given knot exterior or has
essential boundary. These are distinct integration obligations.

**Bit accounting.** Explicit input lists, option generation, polynomial envelope
construction, all intermediate combinations, coordinate arrays, elimination,
integer costs, witness paths, and checking are charged. A Bell-sized initial
list still has Bell-sized input cost. Packed integers do not make exponentially
many bits constant-time operations.

**Conditional endpoint.** Polynomial auxiliary costs plus
`lambda_max=O(log^2 n)` suffice for quasi-polynomial search; the latter hypotheses
are not proved for all knot diagrams. The delivery changes the useful structural
parameter, not the status of a general recognition theorem.

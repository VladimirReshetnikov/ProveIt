# Marked periodic tableaux with independent width and height padding

This note proves a constructive acceptance-interface theorem for the
[cyclic-quotient proposal](EXPLORATION_LIFE_CYCLIC_QUOTIENT_OBSTRUCTION.md).
It changes the local problem from a prescribed Life target to a marked
periodic tableau. No arithmetic operation count, numerical input compiler,
fixed Life simulation, or improvement to the universal bound is claimed.

## 1. The uniform theorem and its precise scope

From a deterministic Turing machine M and finite input word w, one can
effectively construct a finite alphabet A, a translation-invariant
radius-one local relation R, and a distinguished symbol X, such that:

1. M halts on w if and only if there is a totally periodic configuration
   over A satisfying R and containing X.
2. If M halts on w, there exist integers M0,N0 such that for **every**
   width M>=M0 and height N>=N0 there is an M-by-N torus presentation
   satisfying R and containing X. All local tests include both seams.

The alphabet and relation are effectively generated from the machine
and input. They are not asserted to be one fixed small scalar predicate.
The local relation reads a 3-by-3 window, rather than using an unproved
recoding into Wang tiles or fixed-size macrocells. In particular the
padding assertion refers to actual cell dimensions of this relation.

Use the usual two-sided tape model. Normalize the machine to have a
finite tape alphabet Gamma with blank square, a start state q0, and a
unique absorbing halt state qh. Every transition is defined and has
the form

    delta(q,a)=(q',a',d), d in {-1,0,1},
    delta(qh,a)=(qh,a,0).

An undefined transition of the original machine becomes a stationary
transition into qh. Thus this normalization preserves halting, possibly
adding one step. Empty input is represented by one blank under the head.
Write the resulting nonempty input as w0...w[l-1], with l>=1.

## 2. Two boundary tracks and a genuine marker

Every cell has two bits v,h. Local constraints require

    v(x,y)=v(x,y+1),       h(x,y)=h(x+1,y),
    not(v(x,y)=v(x+1,y)=1),
    not(h(x,y)=h(x,y+1)=1).

Thus v marks vertical lines, h marks horizontal lines, and adjacent
parallel lines are forbidden. Cells with v=1 or h=1 carry no tape or
initialization payload. There is exactly one symbol for each of their
three bit pairs: vertical boundary, horizontal boundary, and X=(1,1).
Interior cells have v=h=0.

The requirement that X occur is part of the acceptance predicate.
It is not replaced by local validity alone. Unframed, headless periodic
configurations may satisfy the local relation, but they have no X and
are not accepted.

Suppose a periodic valid configuration contains X at (0,0). Full-rank
periodicity supplies positive horizontal and vertical periods: for
lattice generators (a,b),(c,d), their nonzero determinant gives such
axis periods by integer linear combinations. Hence a next vertical
line x=r>0 and a next horizontal line y=s>0 exist. Choose the nearest
ones. The propagation rules make the open rectangle

    0<x<r, 0<y<s

entirely interior. It has a first row y=1 and a last row y=s-1, and at
least one interior column and row. This is a finite closed tableau;
the marker cannot merely lie at the corner of an unbounded unframed
computation in a periodic witness.

## 3. Exact initialization, with freely chosen blank margins

Each interior cell carries a tape symbol and either no head or one state.
On a first interior row, detected by h(x,y-1)=1, it also carries one of
the phases

    L, I0,...,I[l-1], R.

On every other interior row the phase is absent. The first interior
column must have phase L and the last must have phase R. Allowed adjacent
phases on a first row are exactly

    L->L, L->I0,
    Ii->I[i+1] for 0<=i<l-1,
    I[l-1]->R, R->R.

L and R cells are blank and headless. Phase I0 has symbol w0 and head
state q0; phase Ii for i>0 has symbol wi and no head.

A finite path from L to R in this phase graph necessarily has the form

    L^a I0 I1 ... I[l-1] R^b,       a,b>=1.

Therefore every first row is exactly the intended finite input with one
head and some positive blank margin on either side. There is no second
input occurrence, extra head, or arbitrary tape data. The finite phase
alphabet depends effectively on w; a long input does not increase the
local radius.

## 4. Exact transitions and acceptance at the top

When the next row is interior, its tape payload is determined by the
three payloads immediately below and diagonally below it. A border
neighbor is treated as a blank cell without a head for this calculation.
The following explicit radius-one rule is the usual single-head update:

* The new tape symbol is unchanged if the old center is headless;
  otherwise it is the symbol written by its transition.
* A new head at the center can come from the old left head moving right,
  the old center head staying put, or the old right head moving left.
  Its state is the corresponding transition's new state.
* No incoming head gives no new head. Two or more incoming heads are
  forbidden.

Additionally, forbid an interior head whose transition would move left
through its adjacent vertical boundary or right through that boundary.
This last clause is essential: without it a head could disappear, leaving
a headless top row that would vacuously pass the acceptance condition.

On a last interior row, detected by h(x,y+1)=1, every head that occurs must
be in state qh. No transition is checked across the horizontal boundary.
An initial row may also be a last row; then its initialized head must
already be halted.

Starting at the unique initialized head, induction on the finite rows
proves that each row contains exactly one head and is the exact machine
configuration on this finite interval. The no-escape clause preserves
the head even at an interval endpoint. The local update neither creates
an uncaused head nor changes a cell outside the head's transition.
Extending the interval by blank tape therefore gives the genuine
two-sided machine run, since no step leaves it. The last row's unique
head must be in qh. Thus every periodic marked witness proves that M
halts on w. This argument is independent of the witness's periods and
does not require that different rectangles use identical margins.

All clauses above fit a radius-one window: track propagation, phase
adjacency, the row immediately above or below a boundary, neighboring
heads, and the two vertical side boundaries. Since the alphabet is finite,
the clauses are an effectively enumerable finite forbidden-window list.

## 5. Every sufficiently large pair of dimensions works

Suppose the normalized run reaches qh after t>=0 transitions. Let its
head start at tape coordinate0; the input occupies 0,...,l-1. During
the finite run let the visited head coordinates have minimum e and
maximum f. Set

    a=max(1,-e),        b=max(1,f-l+1),
    M0=a+l+b+1,         N0=t+2.

For any M>=M0, N>=N0, use one vertical line x=0 and one horizontal line
y=0 on the M-by-N torus. Its M-1 interior columns initially contain

    L^a I0 ... I[l-1] R^(b+M-M0).

Place the head at physical column a+1. The whole genuine run stays
inside columns1,...,M-1: its relative tape interval is
[-a,l+b+M-M0-1], which contains every visited coordinate and the input.
Fill rows1,...,t+1 with the genuine initial-through-halted configurations.
Fill every remaining interior row with the same halted configuration.
The absorbing transition makes these padding rows exact transitions.

All boundary, initialization, update and acceptance tests hold, including
those read across either torus seam. No update is required across the
horizontal boundary row. The unique crossing is X. Width padding adds
only blank columns; height padding adds only absorbing halt rows. Their
amounts are independent, proving the advertised property for every
M>=M0 and N>=N0. The thresholds need not be computable from a nonhalting
input; they are used only in the completeness proof after a finite run
exists.

## 6. Consecutive periods and the cyclic interface

Choose m so large that m+1>=M0 and m>=N0. Section5 supplies a valid
(m+1)-by-m torus. The map

    (i mod (m+1),j mod m) -> m*i+(m+1)*j modulo m(m+1)

is an isomorphism and preserves the ordered local offsets. It yields
a cyclic word containing X whose horizontal and vertical strides are
m and m+1. Conversely, a cyclic word of any positive length T satisfying
this marked local relation with these strides pulls back to a periodic
marked plane configuration. Surjectivity follows from (-k,k) mapping
to k modulo T, so the marker is not lost. Section4 then gives halting.

Consequently halting reduces uniformly to this marked cyclic local
problem, with an existential positive stride m and existential length T.
Completeness can choose T=m(m+1); soundness does not need to enforce that
equality. In radix B the two shift multipliers are W=B^m and B*W.

This supplies the padding theorem left conditional in the cyclic-quotient
note for a newly constructed finite local relation. It does not supply
that theorem for Life, nor does it convert arbitrary Life targets into
this relation. Testing alphabet membership, the radius-one constraints,
marker occurrence, and the encoded machine/input all remain arithmetic
compiler obligations. No fixed-scale Wang or cellular-automaton recoding
is used, because it could multiply both periods and invalidate the
consecutive-dimension claim.

## 7. Reproducible bounded evidence

[The checker](../verification/explore_marked_periodic_tm_padding.py)
implements the stated local clauses directly. It constructs padded tori
for several different halting runs, tests rectangular repetitions,
checks finite initialization paths and exact single-head updates,
checks the cyclic reindexing, and exhibits the false head-escape tableau
accepted if the explicit escape prohibition is removed. It also checks
that locally valid unframed configurations have no accepting marker.
The adjacent JSON records fresh finite evidence separately from this
general uniform proof. No infinite search is used to decide halting.

Author and independent complete scoped proof/source review pass. A fresh
independent checker run exactly matches the saved receipt. The general
finite-alphabet proof remains distinct from the bounded binary-tape
machine examples used by the checker.

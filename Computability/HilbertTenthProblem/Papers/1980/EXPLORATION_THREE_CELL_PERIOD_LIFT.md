# A three-cell window lift preserving every period

Every finite radius-one relation can be represented by a relation on
the current cell, its right neighbor, and its next-row neighbor. The
alphabet becomes larger, but the transformation changes neither the
physical cell dimensions nor the exact period lattice. For the marked
Turing tableaux, slightly larger blank margins also give one fixed
accepting window state. Thus the independently padded halting theorem
transfers to this three-cell relation.

This is a finite-alphabet interface theorem. Its alphabet and constants
depend effectively on the machine and its compiled input; this note
does not assert a fixed-index raw-input arithmetic certificate or any
operation count. The [checker](../verification/explore_three_cell_period_lift.py)
and adjacent [receipt](../verification/explore_three_cell_period_lift.json)
record bounded evidence separately from the general proof below.

## 1. The window alphabet and two overlaps

Let `A` be a finite alphabet and let `R` be a subset of `A^([-1,1]^2)`.
An old valid configuration `a:Z^2->A` has its centered3-by-3 window in
`R` at every position. Use the finite alphabet

    B=R.

For three window states `b,c,d` in `B`, define `R3(b,c,d)` by

    c(u,v)=b(u+1,v),  u=-1,0, v=-1,0,1,
    d(u,v)=b(u,v+1),  v=-1,0, u=-1,0,1.               (1)

The order is center, right, next. A block field satisfies this relation
at every position when (1) holds for

    b=b(x,t), c=b(x+1,t), d=b(x,t+1).

Membership in `B` includes the original local predicate. It must not be
replaced by using every3-by-3 block as an untyped state. Empty `R` simply
gives no valid configuration; no nonemptiness assumption is needed.

## 2. Exact reconstruction and exact period lattices

Define the lift and middle projection by

    Lift(a)(x,t)(u,v)=a(x+u,t+v),
    Project(b)(x,t)=b(x,t)(0,0).                       (2)

An old valid configuration clearly lifts to a valid block field, and
`Project(Lift(a))=a`. Conversely take a valid block field. Horizontal
overlap at `(x,t)`, or at `(x-1,t)` for a negative offset, gives

    b(x,t)(u,v)=b(x+u,t)(0,v),  u=-1,0,1.

Vertical overlap similarly gives

    b(x+u,t)(0,v)=b(x+u,t+v)(0,0).

Therefore `b=Lift(Project(b))` component by component. Because each
block belongs to `R`, its projected configuration is old-valid. These
maps are inverse bijections between the two configuration spaces.

Both maps commute with every translation. Consequently, for every
valid configuration and every integer vector `(s,t)`,

    (s,t) is a period of a iff it is a period of Lift(a).             (3)

This is equality of the entire period lattice, including any oblique
periods and any smaller-than-presented periods. The proof works on any
quotient of `Z^2` as well: positions that coincide in a small quotient
are simply read as the same position. In particular, widths or heights
1 and2 require no exception. Every rectangular torus presentation of
the old relation corresponds bijectively to one with exactly the same
dimensions for the new relation.

## 3. One fixed accepting block for the marked tableau

Apply the lift to the original
[marked Turing tableau](EXPLORATION_MARKED_PERIODIC_TM_PADDING.md).
Its unique boundary payloads are the intersection `X`, the vertical
boundary `V`, and the horizontal boundary `H`. Let `Q` be a blank,
headless interior cell with no initialization phase; let `L0,R0` be
blank, headless interior cells with initial phases `L,R`, respectively.
The following single row-major window is a fixed member of `B`:

    Q   V   Q             relative row -1
    H   X   H             relative row  0
    R0  V   L0            relative row +1.             (4)

Call it `X3`. Its central boundary test holds directly: the vertical
track continues into `V`, the horizontal track continues into `H`,
and neither parallel boundary has an adjacent copy. In particular
`X3` is effectively available whether or not the machine halts. Its
symbols depend only on the compiled alphabet, not on a halting run.

A valid block configuration containing `X3` projects to a valid old
configuration containing `X`. Thus any periodic witness containing
`X3` proves genuine halting by the old tableau soundness theorem.
The converse requires the stronger margins proved next. We do not
claim that every old occurrence of `X` already has window (4).

## 4. Independent padding with an unchanged marker window

Suppose the normalized machine halts after `t>=0` transitions on its
nonempty normalized input of length `ell>=1`. The initial head is at
tape coordinate0. Let `e,f` be the minimum and maximum visited head
coordinates during the initial-through-halted finite run. Choose

    a=max(2,1-e), b=max(2,f-ell+2),
    W0=a+ell+b+1, H0=max(3,t+2).                      (5)

For every `W>=W0,H>=H0`, use one vertical boundary at column0 and one
horizontal boundary at row0, and use the original padded construction
with first interior row

    L^a I0 ... I[ell-1] R^(b+W-W0).

The head begins at physical column `a+1`. The first interior column
has tape coordinate `-a<=e-1`, and the last has coordinate

    ell+b+W-W0-1>=f+1.

Both endpoints are strictly outside every visited head position and
outside the initial input. Only the head can write a square. These
two columns therefore remain blank and headless on every row,
including all repetitions of the absorbing halt row. In particular
the first and last interior columns on the last row have payload `Q`.

The first interior row gives phase `L` at column1 and phase `R` at
column `W-1`. Since `H>=3`, the last interior row differs from the
first and its phases are absent. The neighborhood of `X` at `(0,0)`
is therefore exactly (4), for every independently chosen `W,H` above
the thresholds. All original seam, initialization, transition, and
acceptance constraints still hold. Lifting supplies a valid marked
three-cell torus of the same `W,H`.

Thus, effectively from the machine and input, we obtain a finite
three-cell relation and one fixed marked state such that marked
periodic existence is equivalent to halting. Every halting instance
admits marked torus presentations of every sufficiently large width
and height independently. These existential thresholds need not be
computable from a nonhalting instance.

## 5. Consecutive cyclic presentations

Choose `h` with `h+1>=W0` and `h>=H0`. A torus of width `h+1` and
height `h` has cyclic length `N=h(h+1)` under

    i=-h*x-(h+1)*t modulo N.

Center, right, and next therefore have cyclic offsets `0,-h,-h-1`.
The finite CRT bijection puts the fixed marked block into the cyclic
word without changing the relation. Conversely, for any positive
cyclic length `N` and stride `h`, a cyclic word satisfying `R3` at
these offsets pulls back under the same formula to a periodic plane
configuration. The index map is surjective because `(x,t)=(i,-i)`
maps to `i`. Hence an actual marked cyclic state gives an actual
marked plane state, and the projection proves halting.

Soundness does not require `N=h(h+1)`; that equality is a completeness
choice supplied by independent padding. No fixed-size macrocells are
introduced, so coprimeness of the chosen consecutive dimensions is
preserved. An arithmetic encoding still has to pay for its own
geometry, state typing, relation, marker and positive witnesses.

## 6. Verification scope

The checker independently compares both overlap relations with their
direct six-coordinate definitions, reconstructs arbitrary block fields
on small tori, and checks exact period residues and selected original
relations on larger binary tori. It constructs the strengthened marked
padding on several different halting machines, verifies the original
local tableau rules, checks the single fixed window across all tested
dimensions and repetitions, and tests consecutive cyclic reindexing.
The mathematical proof covers arbitrary finite alphabets and all
quotients; the finite receipt does not decide arbitrary halting.

Independent complete scoped mathematical/source review passes, including
the inverse component reconstruction, the complete period lattice,
the fixed marker's local alphabet membership, and the stronger margin
inequalities for every independently padded width and height. A fresh
independent default run exactly reproduces the saved receipt:524,800
arbitrary block fields,32,768 compatible triples,714 original binary
tori,6,426 rejected one-component corruptions,100 marked padded tori,
100 rectangular repetitions and20 consecutive cyclic presentations.

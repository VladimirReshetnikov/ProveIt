# Fixed local rules with a numerical unary-input interface

This note supplies a fixed-machine input interface for the marked cyclic
tableau construction. The alphabet and all local rules depend on a
semidecision machine, but **not on its positive numerical input x**.
Input x is recovered as the distance between two fixed block symbols,
with distance `t=x+2`. This note by itself has no arithmetic operation
count. It is intended for integration with the unique-start cyclic
compiler and the separately counted raw exponent and endpoint equations.

## 1. A normalized machine with a uniform first step

For any recursively enumerable set S of positive integers, effectively
choose a deterministic machine M with finite alphabet containing three
distinct symbols `0,1,2`, blank0, start state q0, and absorbing halt state
qh. It starts at coordinate0 on the unary word

    tape[-t]=...=tape[0]=1, all other cells blank,
    head=0, state=q0, t=x+2.

Its first transition is always

    delta(q0,1)=(q1,2,-1),

where q0 and q1 are distinct nonhalting states. The machine never visits
a positive tape coordinate and halts on this input exactly when x is in
S. All transitions are defined; the halt state writes the same symbol
and stays still.

Here is an effective normalization justification. Prepend the displayed
transition to an ordinary one-sided-tape algorithm. The symbol2 marks
the permanent right endpoint, with the original rightmost unary1 counted
in finite control. Scan left through the other ones, compute their number
t on work tracks, subtract2, and simulate a semidecision procedure for
S on that result. Inputs of length less than4 may instead loop. These
are finite tape algorithms; the product of their finitely many tracks
is a single finite tape alphabet. Preserve an endpoint flag on the
origin cell while using its other tracks, and implement an attempted
move past it by the appropriate stationary finite-control step.

For explicit access to a two-sided semidecision procedure, fold its
tape: physical cell `-j`, j>=0, stores simulated cells j and `-j-1`
on separate tracks. Finite control stores the active track. Moves not
crossing the two simulated origin cells move one physical cell in the
appropriate direction. A simulated move from0 to-1 or back changes the
active track at the same physical cell. Thus a one-sided machine can
perform every transition of the original machine. Initialization of
these tracks and unary-to-binary conversion are ordinary finite scans.
This construction changes the fixed machine, never a numeral as x varies.
The specially named q0 and q1 may be fresh prefix states before all
such work. In particular q1 is nonhalting even if S contains all inputs.

## 2. The fixed finite radius-one relation

Use the two boundary tracks and the exact update/no-escape clauses of
[the marked periodic tableau](EXPLORATION_MARKED_PERIODIC_TM_PADDING.md).
The vertical bit propagates vertically, the horizontal bit horizontally,
and parallel boundary lines may not be adjacent. Boundary cells have
no tape or phase payload. Each interior cell has a tape symbol and
either one machine state or no head.

Replace the former input-specific phase alphabet by the **four fixed
phases** `L,I,Q,R`. A phase is present exactly on a first interior row,
recognized by a horizontal boundary immediately at offset(0,-1).
Allowed left-to-right phase pairs are

    L->L, L->I, I->I, I->Q, Q->R, R->R.

The first interior column has phase L and the last has phase R. The
payloads are: L and R blank and headless; I a headless1; Q a1 with
head q0. Consequently each first row is exactly

    L^a I^u Q R^b, a,b,u>=1.                         (1)

No phase count depends on x. Every subsequent row is the exact
deterministic transition, heads may not escape either vertical boundary,
and the head on the last interior row must be halted. These are the
same radius-one clauses as in the previous construction. Induction
from (1) gives exactly one head on every row and a genuine finite
halting computation on unary length u+1. The first row cannot also
be last because q0 is nonhalting.

## 3. Two fixed block symbols

Apply the [exact-period three-cell block lift](EXPLORATION_THREE_CELL_PERIOD_LIFT.md)
to this radius-one relation. Its alphabet consists of all allowed
3-by-3 windows, and its local relation checks horizontal and vertical
overlaps on center, right, and next. The whole period lattice is
preserved. In the displays below the first row has time offset-1 and
the last row offset+1. H is a horizontal boundary with vertical bit0;
other entries have both boundary bits0. A missing phase means none.

The start block S3, centered on Q, is

    H                 H                  H
    (1,nohead,I)       (1,q0,Q)           (0,nohead,R)
    (1,q1,none)        (2,nohead,none)    (0,nohead,none).       (2)

**Every initialized Q in every valid tableau has exactly this block.**
Its immediate neighbors are I and R even when u=1 or b=1, and the
forced first transition fixes the next row. Since q0 is nonhalting,
that next row is interior. The three columns are interior as well.
Conversely the center phase of S3 is Q, so there are no other S3
occurrences.

For u>=3, the first I in (1) has the fixed endpoint block E3

    H                 H                  H
    (0,nohead,L)       (1,nohead,I)       (1,nohead,I)
    (0,nohead,none)    (1,nohead,none)    (1,nohead,none).       (3)

The head starts u columns to its right and, after one step, is still
at least two columns to its right. Thus it affects none of this block's
bottom row. Conversely any E3 occurrence is the first I of an
initialized run, because its left neighbor has phase L. Both blocks
are allowed local windows independently of whether the computation
eventually halts, and S3 and E3 are distinct fixed alphabet symbols.

## 4. The exact cyclic input theorem

Fix t>=3. The normalized machine halts on unary length t+1 if and only
if there exist integers N,h>=1 and a cyclic word of N lifted symbols
such that:

* the center/right/next rule holds with offsets `0,-h,-h-1`;
* its unit symbol is S3, and no other index carries S3;
* `h*t<N`, and its symbol at index `h*t` is E3.

**Soundness.** Pull the word back to the plane by assigning index
`-h*x-(h+1)*y mod N` to position(x,y). Exact overlap reconstructs a
valid original tableau. It has horizontal and vertical period N.
At(0,0), S3 puts Q on an initial row with a horizontal boundary at
y=-1. Track propagation makes the whole row y=0 an initial row except
at vertical boundaries. A vertical boundary exists on either side:
otherwise the periodic phase row would contain a cycle through Q in
the displayed phase graph, but no such cycle exists. Periodicity also
supplies the next horizontal boundary. Thus Q belongs to a finite
initialized computation rectangle.

Walk left from this Q through positions `(-j,0)`, 1<=j<=t. Their
indices are the distinct nonzero integers `h*j<N`. None is S3, so
none can be another initialized Q, by (2). The endpoint E3 at(-t,0)
is the first I of some initialized rectangle. If it were in a different
rectangle to the left, walking to it would first cross that rectangle's
R region and Q before its I region. This would give another S3 on
the walk, a contradiction. It is therefore the first I of the same
rectangle as the start. The intervening I run has exactly t cells.
The exact transition and no-escape clauses then give a genuine halting
run on unary length t+1, hence membership of x=t-2 in S.

Uniqueness is essential here. Local validity and one start occurrence
alone would allow an endpoint in a different rectangle. The inequality
ht<N prevents a repeat of the distinguished index during this argument;
it does not by itself identify the rectangle.

**Completeness and independent padding.** Given a halting run, write e
for its least visited tape coordinate. Its greatest is0. Use fixed right
blank margin b=2 and any

    a>=a0=max(2,1-e-t), W=a+t+4,
    H>=H0=max(3,number_of_transitions+2).               (4)

Place one vertical boundary at column0 and one horizontal boundary
at row0 on the W-by-H torus. Its first row is `L^a I^t Q R^2`;
the head is at physical column `a+t+1=W-3`. Native tape position z
is physical column `z+W-3`. The leftmost interior native coordinate
is `-a-t`, strictly less than both e and -t. The two right blank cells
are never visited. Fill the finite run and then repeat its absorbing
halt row. This proves local validity for every independently large W,H,
including the seam tests.

Choose h so large that `W=h+1` and `H=h` satisfy (4), and let
`N=h(h+1)`. The head column is `xS=h-2` and the endpoint column
`xE=h-t-2`; both have row1. The map

    i=-h*(x-xS)-(h+1)*(y-1) mod N                     (5)

is a bijection from this torus to the cyclic indices, since h and h+1
are coprime. It sends S3 to0 and E3 to ht; choosing a>=2 gives
`h>=t+5`, in particular `ht<N`. There is exactly one initialized Q
in the torus and therefore exactly one S3 in the cyclic word. The
lift preserves validity and all periods, giving the required word.

## 5. Arithmetic interface and evidence boundary

For a fixed S, enumerate the finite block alphabet and its three-cell
relation once. Put S3 first and E3 last; their indices and every compiler
numeral are independent of x. In outer radix B, `P=B^h`, `q=B^N`,
and a suffix starting at exponent ht begins with E3 exactly when the
endpoint pin identifies that digit. The exponent required by this
theorem is `Wendpoint=P^(x+2)`. The separately proved exponent adapter
uses the fixed offset2. All sufficiently large completeness tori have
`Wendpoint<q`.

[The checker](../verification/explore_fixed_unary_tableau.py) implements
the fixed phase and update rules, checks initialization paths, finite
machine examples at varying unary lengths, both fixed block identities,
independent padding, the cyclic reindexing, rejected truncated runs,
and the necessity of unique-start input identification. These are bounded
checks of the construction. The general machine normalization and the
two directions of the theorem are the mathematical arguments above;
the checker neither decides arbitrary halting nor proves a complete
arithmetic operation count.

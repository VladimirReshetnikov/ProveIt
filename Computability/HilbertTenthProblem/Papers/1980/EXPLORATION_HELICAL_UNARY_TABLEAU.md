# A fixed unary tableau with cyclic offsets 1 and h

The complete84 construction places the right and next neighbors at
cyclic offsets h and h+1. This note changes the finite tableau relation
so that its offsets can instead be **1 and h**. The numerical input
then has endpoint position `t=x+2`, and its power is `B^(x+2)` with
fixed base B, rather than `P^(x+2)` with variable base P. The fixed-base
Pell adapter can reuse the kernel's existing exponent modulus.

The change is semantic: horizontal row-boundary bits propagate only
inside a vertical strip, and vertical boundary cells have one uniform
symbol at every time. Adjacent strips can therefore have different
time origins. This permits a helical cyclic presentation of a finite
halting tableau. The proof does not assume that an ordinary rectangular
torus has a row-major cyclic group structure.

## 1. Fixed machine and local clauses

Use the normalized one-sided machine for a recursively enumerable set S
from [the fixed unary tableau theorem](EXPLORATION_FIXED_UNARY_TABLEAU.md).
It starts with t+1 ones at coordinates -t through0, where t=x+2,
and head q0 at0. Its forced first transition writes the origin flag2
and moves left to a distinct nonhalting q1. It never visits a positive
coordinate and halts exactly when x belongs to S. The machine and all
of the following finite rules are independent of x.

Cells carry vertical and horizontal boundary bits v,hrow. Impose

    v(x,y)=v(x,y+1),
    not(v(x,y)=v(x+1,y)=1),
    hrow(x,y)=hrow(x+1,y) when both vertical bits are0,
    not(hrow(x,y)=hrow(x,y+1)=1).

There is exactly one vertical boundary symbol V: `v=1,hrow=0`, with
no payload. There is exactly one horizontal boundary symbol H:
`v=0,hrow=1`, with no payload. Other cells have both bits0 and carry
a tape symbol and either one head state or no head. There is no
intersection symbol, and no horizontal propagation across a V cell.

The remaining clauses are precisely the fixed unary initialization
and exact machine clauses. A first interior row is detected by H
immediately at offset(0,-1). Its phases follow

    L->L, L->I, I->I, I->Q, Q->R, R->R,

with L at the first interior column and R at the last. L/R are blank
and headless, I is a headless1, Q is a1 with head q0. Thus initialization
is exactly `L^a I^u Q R^b` for a,b,u>=1. Phases are absent elsewhere.
Exact three-neighbor transitions are enforced when the next row is
interior, treating V neighbors as headless blank cells. A head may not
move through a neighboring V. On a last interior row, detected by H
above it, the unique head must be halted.

All these are radius-one finite-window clauses. Horizontal boundaries
are uniform across the interior of each vertical strip because every
pair of adjacent non-V cells satisfies horizontal propagation. They
need not be uniform across the neighboring strips.

## 2. Every marked periodic configuration is a genuine finite run

The two fixed windows S3 and E3 are exactly the interior windows of
the preceding unary theorem. S3 is centered on Q and has rows

    H                 H                  H
    (1,nohead,I)       (1,q0,Q)           (0,nohead,R)
    (1,q1,none)        (2,nohead,none)    (0,nohead,none).

Every initialized Q has this window, even if its I-run or R margin
has length1. The nonhalting q0 forces the next row to be interior.
For u>=3, E3 centered on the first I has rows

    H                 H                  H
    (0,nohead,L)       (1,nohead,I)       (1,nohead,I)
    (0,nohead,none)    (1,nohead,none)    (1,nohead,none).

Every E3 is the first I of an initialization row. These windows read
only interior columns and are unaffected by the changed V symbol.
Both are allowed local windows and are fixed independently of u.

Suppose a periodic valid plane contains S3 at(0,0). Horizontal
periodicity and the phase graph force vertical boundaries on both
sides. Indeed, if none existed, the whole periodic row would be an
initial row, and its phases would give a directed cycle through Q;
the phase graph has no such cycle. Choose the nearest vertical
boundaries. Their propagation makes them the sides of one strip.

Inside this strip the H at y=-1 extends across every interior column.
Vertical periodicity supplies a subsequent H; choose the nearest one.
The region between these boundaries is a finite rectangle. Its first
row is the exact unary initialization, and the transition/no-escape
induction gives a unique genuine head on every interior row. The last
row halts. The argument uses only the boundaries of this strip; it
does not require its neighbors to have the same initialization time.

Apply the exact-period3-by-3 window lift, giving a fixed ternary rule
on center, right, and next. The following is the cyclic input theorem:
for any t>=3, the machine halts on unary length t+1 if and only if
there are N,h>=1 and a cyclic lifted word such that

* the ternary rule holds with offsets `0,-1,-h`;
* S3 occurs exactly once, at index0;
* `t<N`, and E3 occurs at index t.

For soundness pull the word back by index `-x-h*y mod N`. Exact overlap
reconstructs a valid original plane, with axis periods N. The preceding
rectangle argument gives a finite run at the distinguished S3. Along
the leftward path of length t the visited indices are1,...,t, all
distinct and nonzero. No other initialized Q can occur there, since
each would be another S3. If E3 at the end of the path belonged to a
different strip, entering that strip from the right would cross its
Q before reaching its first I. This contradicts uniqueness. Thus E3
is the first I of the distinguished rectangle, and its I-run has
exactly t cells. The run halts on raw input x=t-2. In particular
soundness assumes neither N=hH nor h equal to the physical strip width.

## 3. Completeness by strips with shifted time origins

Suppose the normalized machine halts. Use the same independent
padding as before: if e is its least visited tape coordinate, take

    a>=max(2,1-e-t), w=a+t+4,
    Htime>=max(3,number_of_transitions+2).

Make a base array G on columns0,...,w-1 and times0,...,Htime-1.
Column0 is always the uniform V. At time0 all other columns are H.
The first interior row is `L^a I^t Q R^2`. Put the genuine run into
the next rows and repeat its absorbing halt row. The head column is
`xS=w-3`, and the endpoint column is `xS-t`. The padding places the
whole run strictly inside the strip, with both marker windows away
from the vertical boundary.

Extend it to the plane by

    T(x,y)=G[x mod w, (y+floor(x/w)) mod Htime].       (1)

Inside a strip this is exactly the padded tableau. At a strip edge,
the V symbol has no time-dependent payload and is treated as blank
for updates. Its own clauses ignore the neighboring tape payloads.
Horizontal propagation is disabled there. Thus every seam clause
holds even though the next strip's time origin is shifted by one.
Vertical propagation and nonadjacent boundary clauses also hold.

The plane (1) has periods `(w,-1)` and `(0,Htime)`, hence is described
by the single cyclic index `-x-w*y mod N`, with N=w*Htime. Choose
the arithmetic stride h=w. After translating the origin to the head,
assign base entry G[r,s] to index

    i=-(r-xS)-h*(s-1) mod N,
    0<=r<h, 0<=s<Htime.                               (2)

This assignment is a bijection: reducing the index modulo h determines
r, and then its quotient determines s modulo Htime. Equation(1),
not an ordinary rectangular seam identification, proves that every
original local test holds at every cyclic index. Lift by reading the
actual cyclic windows at offsets `-dx-h*dy`. Their horizontal and
vertical overlaps give the ternary rule at offsets `0,-1,-h`.

The single initialization row has exactly one Q and exactly one first I,
so the lifted cyclic word has one S3 and one E3. Equation(2) sends
S3 to0 and E3 to t. Also t<w<N. This proves completeness with both
markers unique and with the required strictly interior endpoint.

The size w is chosen after the finite run exists and may be arbitrarily
large; the construction does not impose a computable input-only space
bound on the machine. The alphabet and all finite rules remain fixed
before x varies.

## 4. Arithmetic transport and positive quotient

For the native scalar compiler of the84 source, let
`q=B^N,P=B^h,D=q-1,J=D/(B-1)`. The right and next words now satisfy

    Rword=B*C-kR*D, Yword=P*C-kY*D.

Both cyclic words are in(0,D). Their actual local field is

    Factual=DC*C+DR*Rword+DY*Yword.

Consequently the local equation is

    (DC+B*DR+DY*P)C=F+z*D,
    z=DR*kR+DY*kY.                                   (3)

The coefficient `DC+B*DR` is one fixed numeral. Equation(3) costs
the same five operations as before: multiply DY by P, add the fixed
coefficient, multiply by C, multiply z by D, and add F. The coefficient
bound and exact modular recovery of F are unchanged.

Every genuine native cell is at least1, hence C>=J. Thus
`kR=floor(B*C/D)>=1`, and
`kY=floor(P*C/D)>=floor(P/(B-1))>=1` since P>=B.
The transport quotient z is strictly positive. Local occupancy now
propagates directly under shift1 from the inserted Start.

The endpoint exponent is `W=B^t=2^(d*t)`, where d=log2(B) is a fixed
numeral. The separate fixed-base exponent bridge prices multiplication
by d, the strengthened bound, and reuse of the retained base-two
congruence. This note proves the semantic and transport interface;
the complete arithmetic ledger belongs to that integration.

## 5. Reproducible bounded evidence

[The checker](../verification/explore_helical_unary_tableau.py) implements
the relaxed boundary rule directly. It validates padded halting strips,
every helical seam, the two fixed windows, exact lift overlaps, rejected
nonhalting truncations and malformed initial payloads. It also checks
noncanonical strides `h=a*w` with a coprime to Htime, so that h differs
from the physical strip width and N need not be divisible by h. Those
tests support the general soundness contract, whose proof is above.
Ordinary rectangular window lifting is not used at the helical seam.

# Materialized four-coefficient Con(ZFC) instance: 943 signal tiles

> This document contains the shared language/interface proof and the frozen
> 5^11 fallback geometry. The recommended, independently audited 5^10
> instance is specified by `WANG943_COMPACT_LAYOUT.md` and
> `COMPACT_COEFFICIENT_BINDING.json`. Do not mix the two coefficient tuples.

## Result and exact scope

There is a new four-coefficient backend for the same inputless native-window/Pell
arithmetic interface as the T4 package at ProveIt commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. It has

    B = 2^(5^11) = 2^48,828,125,

instead of T4's `2^(5^18)`. Its four actual integer coefficients have been
materialized as unsigned little-endian binary files, not merely described by a
recursive recipe. Their total size is 25,785,236 bytes; their deterministic gzip
representations total 40,315 bytes. The coefficient beta has 48,828,125 bits,
exactly 78,125 times fewer than the T4 beta. K has 59,797,501 bits.

The construction combines four changes: a directed-signal Wang language with
943 tiles, occupied binary edge labels, saturated clause masks, and a shorter
four-anchor configuration. These are coefficient improvements, not new
variable-count, degree, or arithmetic-operation records. Every compatible
arithmetic skeleton must replace all four ports together.

The universal argument is ordinary mathematics, dependent on the existing
inputless arithmetic/compiler theorems and literal K215 calibration. This is
not a fresh end-to-end Lean/Rocq proof, a proof of consistency, a ZFC refutation,
or evidence that K215 halts. Finite verification is distinguished below from
the universal soundness/completeness proof.

## 1. Source and machine convention

The exact table is
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` at the reviewed
commit. Its SHA-256 is

    fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090.

All 430 working actions are retained. Initially the head is in state 0 on an
all-zero, two-sided tape. Working states are 0 through 214; 215 is halt. The
actual first action is `(0,0) -> (write 1, right, state 93)`. An action entering
halt retains its original write and movement. Only after entering halt add
`(215,b) -> (b,stay,215)` for padding.

Upstream Python files are inert source only. The newly authored programs in
this directory do not import or execute them.

## 2. A 943-tile directed-signal language

### 2.1 Vertical and horizontal edge labels

A tile is `(west,north,east,south)`. Adjacent tiles match east to west and
south to north. North/south labels are the old cell codes:

- headless bits 0 and 1;
- `head(q,b) = 2(q+1)+b`, for 0 <= q <= 215 and b in {0,1};
- L=434, Q=435, R=436, V=437, H=438.

The horizontal colors are O=0, HB=1, PL=2, PQ=3, PR=4 and BAD=5, followed by
directed signals. Let SR be the sorted set of states targeted by an original
right-moving action, and SL the analogous left-moving set. Their cardinalities
are 199 and 45. Define

    right(q) = 6 + index of q in SR;
    left(q)  = 205 + index of q in SL.

Thus every horizontal color is at most 249. The numeric reuse of labels
between horizontal and vertical ports is harmless: only like ports match.

### 2.2 Complete finite tile recipe

Include precisely the following tiles:

1. Each working action `(q,b)->(v,right,t)` gives
   `(O,head(q,b),right(t),v)`; each left action gives
   `(left(t),head(q,b),O,v)`. There are 430.
2. The two halt loops are `(O,head(215,b),O,head(215,b))`.
3. The two headless stay tiles are `(O,b,O,b)`.
4. For q in SR and b in {0,1}, include
   `(right(q),b,O,head(q,b))`; for q in SL include
   `(O,b,left(q),head(q,b))`. There are 398+90=488.
5. For c in `{0,1,head(215,0),head(215,1)}`, include `(O,c,O,H)`.
6. Four initialization tiles are

       (PL,L,PL,0), (PL,Q,PQ,1),
       (PQ,R,PR,head(93,0)), (PR,R,PR,0).

7. Three reset tiles are `(HB,H,HB,p)` for p in {L,Q,R}.
8. Nine seam tiles are `(u,V,v,V)` for
   u in {O,HB,PR}, v in {O,HB,PL}, independently.
9. Add the forbidden tile `(BAD,0,O,0)`.

The count is

    430+2+2+488+4+4+3+9+1 = 943.

No two listed tiles coincide. The distinguished Start is `(PL,Q,PQ,1)`.
It is selector 0; Forbidden is selector 1; all others follow lexicographically.
The exact ordered list is `wang943_tiles.json`, SHA-256

    66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f.

BAD occurs as a west color and never as an east color. Therefore Forbidden
cannot occur in any globally matching plane. Forbidding it loses nothing.

### 2.3 Soundness: a marked periodic tiling gives a blank halt

The vertical color V occurs on one side of a tile iff it occurs on both:
the V columns are invariant in time. Consider a Start tile. Its west PL
color can continue left only through initialization L tiles until a V;
its east PQ forces the special first R tile, then PR can continue only
through ordinary R-phase tiles until V. No directed horizontal phase cycle
contains Q. Horizontal periodicity therefore forces V columns on both
sides of the marked Q. Choose the nearest such columns.

The initial row between them is `L^u Q R^v`, where u >= 0 and v >= 1.
Allowing u=0 is harmless and is deliberately not replaced by the stronger
old T4 assertion u>=1. Its predecessor at each interior cell must be an H
tile, since only H tiles produce L,Q,R as south labels. The H row's HB
edges propagate throughout the strip. The initialization tiles implement
the genuine first action exactly: write 1 at Q and put state 93 on the
blank cell immediately to its right.

Between H rows, a working-head tile writes its symbol and emits its target
state in the direction of motion. The adjacent headless tile must receive
that signal and has that state on its south edge. A headless tile with no
incoming signal preserves its bit; a halt tile stays. Two incoming heads
cannot enter one cell, and a head cannot move through a V column because
V accepts no directed state signal. These facts implement one exact machine
step whenever the current row has the unique head supplied by initialization.
Induction preserves that unique head and the literal K215 computation.

Temporal periodicity supplies a subsequent H row. Choose the first. Every
tile immediately above it must be one of the four finish tiles, so the
unique head has state 215. The prohibition on mixing a finish with an
ordinary successor across the strip follows from matching in the following
row: H tiles have HB edges and no ordinary tile does. No global uniqueness
of Start is used for soundness; unrelated periodic components are harmless.

### 2.4 Completeness and helical padding

Given any finite blank halting run, choose finite blank margins with at least
two never-visited cells beside each V boundary. Make a strip with an H reset
row, the initialization row, the actual run after its first action, and any
number of absorbing halt rows. Its width w and height h may be chosen
independently as any sufficiently large integers, in particular powers of 5.

Interior tiles are those in the recipe. At a V seam, its west color is the
last interior tile's east color at time t-1, while its east color is the first
interior tile's west color at time t. These colors belong independently to
{O,HB,PR} and {O,HB,PL}; all nine pairs were included. Its vertical labels
are always V. Thus the extension

    tile(x,t) = G(x mod w, (t + floor(x/w)) mod h)

matches even across the time-shifted seam. The required margins prevent any
head signal from reaching the seam. The periods are (w,-1) and (0,h).
For N=wh, the cyclic coordinate

    i = -(x-x_Start) - w(t-1) modulo N

has Start at 0, right neighbor i-1 and temporal neighbor i-w. This chosen
witness has exactly one Start and no Forbidden. Width and height still
admit all independent padding required by the native dummy-control theorem.

Conversely, an arbitrary cyclic tile word satisfying the two edge matchings
at shifts -1 and -h0 pulls back to the plane `tile[-x-h0*t]`. This argument
needs neither h0|N nor coprimality, and remains valid when residues collide.
Start's north Q and south 1 exclude temporal shift zero modulo N.

Therefore a marked periodic Wang tiling exists iff blank K215 halts.

## 3. Exact coefficient recipe

All letters in this section are fixed integers, not existential unknowns.
Set

    k=943, a=10, ell=10, A=1024,
    b=625, rho=2^625, Lcell=78125,
    d=b*Lcell=48,828,125=5^11, B=rho^Lcell.

For each of the four labels x in a tile, encode `x+512` in ten bits. Write
bit_j(x+512) for its j-th binary digit, 0<=j<=9. The high bit is the
occupancy bit; the lower nine bits are the edge label. In slot order
west,north,east,south put

    e_0(j)=1023+j, e_1(j)=1013+j,
    e_2(j)=1003+j, e_3(j)=983+j.

The native exponent set E is the disjoint union of

    selectors 0..942;
    these forty copy positions;
    dummy positions 1063,1064;
    anchors 1095,2190,4380,9855.

It has exactly 989 positions. For tile i with slot labels x_it define

    c_i = 1 + sum_(t=0..3,j=0..9) bit_j(x_it+512) A^(1+10t+j)
              + sum_(j=41..44) A^j;
    c_e_t(j) = A^(1+10t+j);
    c_1095=A^41, c_2190=A^42, c_4380=A^43, c_9855=A^44;
    c_1063=c_1064=0.

The saturated clause mask is the manageable 528-bit integer

    mu = A-2 + sum_(j=1..44) (A-3) A^j + 2^450 (2^78-1).

Its population is `9+44*9+78=483`. Finally set

    DC = rho^30 + rho^17571 + rho^3285 + rho^7665
         + sum_(e in E) c_e (rho^(37272-e)+rho^(56986-e));
    DR = rho^17551;
    MF0 = mu(rho^37272+rho^56986)
          + sum_(j=0..9) rho^(1013+j)
          + sum_(j=0..9) rho^(17551+1023+j)
          + rho^4380 + rho^9855;
    MC = B-1 - sum_(e in E, e != 1) rho^e - 2rho^1063;
    MF_native = MF0+4.

The four actual arithmetic ports, in the established order, are

    beta=B-1, K=DC+B*DR, MC, MF_source=MF_native+B-1.

In particular MF_source is NOT MF_native. No member of this four-tuple
may be mixed with T4's tuple or with its tile ordering.

## 4. Why binary occupied labels and saturated masks are valid

### 4.1 Selector and copy decoding

Native masks give Boolean digits at selectors, copies and anchors, with the
single ignored dummy allowed digits 0..3. The other dummy is Boolean. A
clause sum `sum c_e d_e` has no carries in base A: its units digit is at
most 943 and each other digit is at most 944, strictly less than A=1024.
All c_e on dummies are zero.

The low mask A-2 allows only 0 or 1 for the selector count. Thus a cell is
empty or selects exactly one tile. For each copy bit the corresponding
digit is `selected tile bit + copy bit`, and for each anchor it is
`selector count + anchor bit`. The mask A-3 allows exactly digits 0 or 2.
Consequently in an empty cell all copies and anchors are zero; in an
occupied cell all forty copy bits match its tile and all four anchors are
one. This is exactly the old parity decoder, strengthened by bits that
valid sums never use. Saturation does not exclude any valid cell.

The 78 high padding bits begin at bit 450. Every possible clause sum is
strictly less than A^45=2^450, even before selector extraction. Hence
these extra tested bits are identically zero and add no condition.

At the overlap tests, the sum of two Boolean copy bits must be even, so
the corresponding bits match. In particular the occupancy bit on each
horizontal edge propagates occupation from Start through the whole cyclic
word, because the spatial shift is one cell. This replaces the occupancy
argument previously supplied by one-hot edge encodings. All forty bits
then give exactly east=neighbor-west and south=temporal-neighbor-north.

### 4.2 Balanced populations and low congruences

The two clause bands contribute 966 mask bits. Twenty binary overlap tests,
two anchor tests, and the added low bit contribute 23 more:

    pc(MF_native)=2*483+20+2+1=989.

The data mask removes 988 native low bits (all except selector 1), plus
the upper bit of the distinguished dummy. Therefore

    pc(MC)=d-989, pc(MC)+pc(MF_native)=d.

Also `0<MC,MF_native<B-1`, `MC=2 mod4`, and `MF_native=4 mod8`.
Thus the shifted inverse-population argument and its exact two-bit surplus
are unchanged. The canonical low-origin field test is unchanged as well:
DC and DR have positive degree, so the unit digit comes only from a
temporal-neighbor Start; the canonical origin is not its own temporal
neighbor. The new dense bits lie far above the low field bits.

## 5. Geometry, carries and synchronization

Put M=1095, Emax=9M=9855, Hc=16M+31=17551,
T1=37272 and T2=56986. Every native exponent, including the potential upper
dummy spill position, lies in [0,Emax].

The exact field targets are:

- at 1013+j, shift 30 contributes current-south bit j and the temporal
  rotation contributes neighbor-north bit j;
- at Hc+1023+j, shift Hc+20 contributes current-east bit j and DR times
  the spatial shift contributes right-neighbor-west bit j;
- at 4M and 9M, shifts 3M and 7M contribute the current M and 2M anchors,
  respectively, together with the rotated 4M and 9M anchors.

No other bare shift hits these 22 targets. Every target is below
T1-Emax=27417, so no reflected clause coefficient contaminates it. At a
clause target T1 or T2, the unshifted contribution is exactly `sum c_e d_e`.
The other band cannot contribute there because

    gap=T2-T1=19714 > 2Emax=19710.

The two possible rotation-hit sets `(T1-E) mod Lcell` and
`(T2-E) mod Lcell` are disjoint, including the extra spill position. Thus
every binary rotation leaves at least one clean clause band.

Let mass=(989+2)(2 sum c_e+6). It has 461 bits; the maximum of
`4mass+8`, `2mu+4`, and 16 has 529 bits. Hence rho=2^625 exceeds every
uniform no-carry threshold required by the existing proof. The bound also
covers the upper dummy bit during non-radix-aligned rotations. Unshifted
degrees are below Lcell, because T2+Emax=66841<78125.

Write a binary rotation as bt+epsilon, 0<=epsilon<b. For
1<=epsilon<=b-2 all rotated radix digits are even. For epsilon=b-1 only
the one upper-dummy spill position can have an odd digit. The two distinct
anchor tests at Start require odd digits at both 4M and 9M, excluding
both cases. Thus epsilon=0.

For aligned rotation, the only native support pair with difference
`9M-4M=5M` is `(4M,9M)`. All nonanchors are below M; the other anchor
differences are M,2M,3M,7M,8M. There is no circular wrap because the
circumference exceeds twice the support span. Hence t=0 modulo Lcell.
This is the same whole-cell synchronization argument as T4 with a shorter
valid anchor ruler, not an assumption of alignment.

For the five-adic tuning, b is a power of five and so rho=2 mod5. Since
the band gap is 2 mod4, every paired clause contribution cancels mod5.
The four bare terms give

    2DC-DR = 4 mod5,

a unit. The retained dummy-control theorem therefore adjusts the ACTUAL
packed rank to the required temporal-stride congruence. It does not treat
that exponent as an independently chosen witness. The formula for the
effect of a low dummy bit is unchanged, with this tuple's DC,DR and
distinguished dummy exponent 1063. Arbitrary sufficiently large power-of-five
width and height padding supplies all its no-wrap and size hypotheses.

All native digit coefficients remain within the old carry bound, giving
strict positive raw slack. The established inputless Pell/population
arithmetic now decodes precisely the marked Wang plane in Section 2; its
canonical witnesses construct the reverse direction. Combining that
equivalence with the imported exact K215 endpoint gives the intended
ZFC-formalizable statement that existence of a solution is equivalent to
a finite ZFC refutation, and unsolvability is equivalent to Con(ZFC).

## 6. Materialized integers and checks

`coefficients/{beta,K,MC,MF_source}.bin` are minimal-byte unsigned
little-endian integers, without headers. They are the literal integers in
Section 3. The matching `.bin.gz` files decompress byte-for-byte to them.

| Port | Bits | Bytes | SHA-256 |
|---|---:|---:|---|
| beta | 48,828,125 | 6,103,516 | e28f57168b1a998dedd9cf3bd8e6b2c8af7aec2c0ae45d028b13a5c6f0fcaaa1 |
| K | 59,797,501 | 7,474,688 | 3b5eb39456901c2e3141687ac6a4fc60d60d3222e0ca675868455da89073c0b2 |
| MC | 48,828,125 | 6,103,516 | 5cf159802f4bfba8c2518e9b1359ba8e274435f2d7685eb6269a34d64b3bbd70 |
| MF_source | 48,828,126 | 6,103,516 | b0759e49bda30c5833ce6e3550451a779a2cff2d9d6db2ca7285a6cca2c01dc2 |

The independently authored semantic checker reconstructs all 943 tiles in
their exact order without importing the builder. It also checks 425 padded
helices across 17 explicit finite halting-control machines, with 33,800
local tiles and both edge matchings. The first action stays authentic and
the action entering halt retains its movement. These are seam tests, not
K215 halting experiments.

The scalar checker exhausts the actual support's 22 target identities,
the all-rotation band and anchor intersections, exact population and
carry bounds, and the five-adic unit. The materializer reads its actual
binary output back and checks the coefficient identities, populations,
low congruences, bit lengths, gzip round trips and SHA-256 hashes.

Reproduction, using only newly authored files:

    python -B build_wang943.py
    python -B check_wang_helices.py
    python -B materialize_wang943.py

Finite tests supplement Sections 2–5; they do not replace the universal
arguments or the imported arithmetic and foundational theorems. An
independent review and byte-for-byte reconstruction are recorded separately.

## Source links

- [Reviewed T4 adapter](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4/bridge/BRIDGE_AUDIT.md).
- [Reviewed T4 report](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4/report.tex).
- [Exact literal K215 machine](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm).
- [K215 endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/f0ae4e0991ca44a7bb4e5671d42e33d775e48035/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean).
- [Inputless 06 source at its historical pin](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/report.tex).



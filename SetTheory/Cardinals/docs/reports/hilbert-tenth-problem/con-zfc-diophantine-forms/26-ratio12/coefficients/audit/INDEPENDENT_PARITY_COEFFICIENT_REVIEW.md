# Independent review of the parity-separated Wang943 coefficient tuple

Reviewed 22 October 2026. The inherited language and coefficient interface
are from ProveIt snapshot `a477d0fc8b6feda53796835564a988015e744d4d`.
The new complete tuple is under `research/compiler/delivery_parity/`.

## Verdict

The parity layout is a valid replacement for the compact Wang943 geometry,
relative to the inherited native compiler theorem. I independently checked
the universal finite-support arguments, the carry/mask hypotheses, and the
whole-tuple bytes. The new native spatial displacement Hc=1 is compatible
with the unchanged whole-cell spatial displacement supplied by the factor B
in K=DC+B*DR. These two displacements must not be conflated.

The source language, ordered943-tile list, clause coefficient values, mask
decoder, helical padding, and literal K215 machine are unchanged. The new
layout changes copy positions, field target positions, DC, DR, and both
masks coherently. It is not legitimate to mix a mask or K with an earlier
tuple merely because beta is unchanged.

## 1. Literal support and exact tested positions

The native support is

    E = S union {2195,3296},
    S = {0,...,942} union {960,962,...,1038}
        union {1063,1064,1095,1096}.

Its size is989 and its maximum3296. The four copy groups W,N,E,S start
at1020,1000,980,960, respectively, with step2. The bare DC shifts are
40,41,1100,2200; DR=rho has native displacement1. The bands remain
T1=7631,T2=8733, with rho=2^625 and cell length15625.

At a vertical target1000+2j:

- shift40 sees exactly the current south copy960+2j;
- shift41 would need the absent odd position959+2j, all of them above942;
- DR would need the absent odd position999+2j;
- the temporal native support contributes exactly north copy1000+2j.

At a spatial target1021+2j:

- shift41 sees exactly the current east copy980+2j;
- shift40 would need the absent odd position981+2j;
- DR sees exactly west copy1020+2j;
- the target is odd and absent from the native support, so the temporal
  summand contributes nothing there.

The two larger bare shifts miss every copy target. At2195, shift1100 sees
only1095, while at3296, shift2200 sees only1096. The other bare shifts and
DR miss those anchors; the temporal terms are the anchors2195 and3296.
The smallest reflected-clause exponent is7631-3296=4335, above every
tested copy/anchor target. Thus no clause term contaminates these tests.

At each clause target, every bare shift and DR misses the native support.
Interference from the other reflected band would require a support
difference1102, which does not exist. The clause contribution therefore
remains exactly the unchanged sum of native clause coefficients.

These identities hold for all possible native digit assignments by
linearity. They are not merely tests on the selected canonical tableau.

## 2. Every rotation: clean bands and synchronization

A pair of elements within S has difference at most1096. The only larger
support elements are2195 and3296. Subtracting1102 from them yields1093
and2194, both absent. Hence no support pair has difference1102. The
circumference15625 exceeds twice the support span, so no additional
circular case arises. Therefore

    (7631-E) mod15625 and (8733-E) mod15625

are disjoint. The potential upper-dummy spill exponent1064 is already
in E, so this statement also includes the expanded support. At least
one clause band is uncontaminated for **every** temporal bit rotation.

For the anchor difference1101, subtracting it from2195 gives1094, absent;
subtracting it from3296 gives2195, present. Thus the only support pair
with that difference is(2195,3296). Equivalently the two circular
anchor-hit sets intersect exactly at0.

The inherited no-carry estimate lets the clean clause decode the marked
cell and its four anchor bits. Write a temporal bit displacement as625t+e,
0<=e<625. If1<=e<=623, every rotated native radix digit is even. For
e=624, only the single upper-dummy spill position can contribute an odd
digit per cell. The two distinct marked anchor tests require odd digits
at both2195 and3296. Thus neither case is possible, and e=0. The unique
anchor-hit intersection then forces t=0 modulo15625, giving whole-cell
temporal alignment. No additional stride assumption has been inserted.

Once aligned, the copy targets impose exactly south=current versus
north=temporal neighbor and east=current versus west=spatial neighbor.
The occupied high bit propagates nonemptiness along the whole-cell
spatial shift of one, just as in the inherited Wang943 proof.

## 3. Carry bounds, masks, and the special origin

Only positions changed. The multiset of clause coefficient values and
the989-position support count are unchanged. The clause sum is below
A^45, with A=1024; every base-A coefficient digit is at most944. The
uniform mass

    mass=(989+2)*(2 sum(c_e)+6)

has461 bits. The maximum of4mass+8,2mu+4,16 has529 bits, well below
rho=2^625. Thus the inherited bound for arbitrary rotations and the
extra dummy bit continues to apply. The strict raw-slack inequalities
3rho/4+mass<=rho-2 and rho/2+1+mass<=rho-2 also hold unchanged.

Every reflected exponent is positive. The largest unshifted DC product
exponent is8733+3296=12029<15625; the largest DR product exponent is
3297<15625. Consequently no unshifted convolution spills between cells
before the intended whole-cell shifts.

The field mask has2*483+20+2+1=989 bits. The data mask clears988 native
low bits and the upper dummy bit, also989 bits. Their supports are
internally disjoint and below the cell cutoff. Hence the native masks
obey

    pc(MC)+pc(MF_native)=d,
    MC=2 modulo4, MF_native=4 modulo8,
    0<MC,MF_native<B-1.

DC has least native exponent40 and DR has exponent1, both positive.
Therefore the unit radix digit of the canonical field still comes only
from the temporal-neighbor Start selector. The canonical origin is not
its own temporal neighbor, so the inherited special-origin test remains
valid. Shrinking Hc has not introduced a constant DR term.

## 4. Five-adic tuning and canonical restrictions

Since rho=2 modulo5 and the band gap1102 is2 modulo4, paired reflected
clause terms cancel modulo5. The bare shifts give

    DC=2^40+2^41+2^1100+2^2200=0 modulo5,
    DR=2 modulo5,
    2DC-DR=3 modulo5.

This is a unit, as required. The actual-rank dummy derivative is2 modulo5.
The canonical dummy changes preserve every tested target, both origins,
and the strict slack. The independent power-of-five width and height
padding is a property of the unchanged Wang language. Therefore the
odd-i, odd-s, square-w completeness construction used in the24-integer
arithmetic proof remains compatible with this new whole tuple.

## 5. Independent literal reconstruction

`audit_parity_cross_agent.py` imports no builder, materializer, or prior
auditor. It reads only the pinned inert ordered tile list, reconstructs
every clause coefficient from the ten-bit occupied labels, checks all
69,230 native-basis convolution identities, the two universal finite
rotation sets, all scalar/carry/mask inequalities, and the exact bytes of
all four coefficient files. It also verifies every gzip round trip.

Results are in `PARITY_CROSS_AGENT_CHECKS.json`. The largest coefficient K
has9,766,251 bits, down from13,201,251 in the old compact tuple. The four
new unsigned minimal little-endian payloads total4,882,894 bytes, down
from5,312,269. Their deterministic gzip files total19,820 bytes. The
common base remains B=2^(5^10), so the reduction is in K's height and
the aggregate literal payload, not in beta or the base exponent.

The reconstruction verifies the numeral recipe, not the unbounded machine
theorem. Its universal decoder/adapter reasoning is given above; the
native compiler, Pell interface, and K215 finite-refutation calibration
remain explicit imported mathematical dependencies. No new Lean/Rocq
certificate or claim of consistency is implied.

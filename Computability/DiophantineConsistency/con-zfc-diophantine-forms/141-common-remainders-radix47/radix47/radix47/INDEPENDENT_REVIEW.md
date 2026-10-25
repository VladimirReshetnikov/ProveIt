# Independent ordinary and finite review of complemented radix47

Reviewer: a separate research agent, 25 October 2026.
Repository snapshot: `55d1f72aedebf892e446c90d35fa1ae37689b0f2`.
New artifacts reviewed: `agent_math/radix47/`; retained ordinary parent:
`research/compact66-shared-marker-radix49/README.md` at that snapshot.

## Finding

The complete radix47 adaptation is mathematically valid under the retained
ordinary P66/native-language/K215/refutation calibrations. No new unproved
controller premise is needed. The complement changes the whole coefficient
tuple and the packed witnesses; this is not equality with an old specialized
polynomial. The fifteen positive unknowns, 66 arithmetic operations, and
exact degree 157 remain the inherited P66 profile. The four new raw constants
total 207,214 bytes. This is not a global simplicity or literature-priority
claim and not a new end-to-end proof-assistant certificate.

Label complementation itself has explicit repository predecessors, including
`candidates/split116-compact/compact54/provenance/interface_proof.md`.
The present contribution is its exact composition with the indexed943,
shared-marker language and the complete radix47 carry, padding, controller
and coefficient calculation. The old radix47 local-clause obstruction used
an unchanged coefficient array and a permissible carry of93; it does not
apply after the present coefficient change and the proved carry bound29.

## Complete language correspondence

For horizontal labels apply c -> 255-c and for vertical labels apply
c -> 511-c. These are involutions on the complete 8-bit and 9-bit fields.
Apply the same horizontal map to both west and east and the same vertical
map to both north and south. Every edge equality is therefore preserved
in both directions, as is every marked finite or periodic tiling. Preserve
all selector indices, including Start0 and Forbidden1, all four occupancy
bits, all three anchor bits, both dummy positions, and every physical support
position. Start's unequal north/south labels remain unequal. The forbidden
BAD color remains disjoint from the corresponding permitted opposite-edge
colors because the transformation is bijective.

Write u for the old 34-bit concatenated label and u'=2^34-1-u for the
transformed one. The new selector coefficient is exactly

    1+1024(2^34-u')=1+1024(u+1).

Its sum with the old selector coefficient is `2^44+1026`. This identity
provides an independent coefficient reconstruction from the pinned old K
integer, separate from the typed tile-table route. The actual maximum
selector coefficient is 15,049,678,914,561, strictly less than 2^44; the
maximum over every coefficient is 2^44. The generic field bound alone
would allow the larger value 2^44+1, so the actual-table maximum must be
retained as an explicit checked finite premise. It has been checked.

## Carry and local-clause proof

The new complete formal coefficient sum is 3,953,059,820,717,999.
With rho=2^47 and the unchanged zero-coefficient dummy geometry, the parent
predecoded convolution estimate becomes

    sum(c_e)+5+2 max(c_e)+3rho/4+29 < 30rho.

Thus the monotone cyclic carry map preserves the finite box0..29. The
fixed-point/telescoping argument is unchanged, including the exclusion of
the zero/all-ones ambiguity using the source's strict native F bounds.
The two clause hit sets remain disjoint, so at least one is free of a
temporal digit. Its low ten tests now give

    n+k <= 943+29 = 972 < 1024.

Therefore n+k is0 or1 and at most one tile is selected. With the same
seven shared marker weights, the upper tests recover the entire transformed
34-bit label and all seven individual marker bits exactly, by the parent's
counting argument. In an occupied cell the raw aggregate is rho+1.
Its stored digit is1 and its outgoing carry is1. This outgoing carry is
explicitly allowed; it is not silently discarded.

After decoding, there are at most44 nonzero physical inputs per cell.
Using at most88 selector-coefficient hits and the exact nonselector sum
rho-1024 gives

    88 max(c_e)+(rho-1024)+2 max(c_e)+5+3rho/4+29
      =13rho-990 <13rho.

Hence every outgoing carry is at most12. This bound includes the occupied
clause's carry1 and all later convolution digits.

## Why carry1 cannot corrupt another test

Every constrained downstream target has its own protected predecessor.
The exact geometry is unchanged and independently recollected:

- The two phase-anchor predecessors have current raw contributions0 and
  x_2195. Even a fractional temporal digit at most3rho/4 and incoming12
  cannot overflow, so both outgoing predecessor carries are0.
- The parent phase proof therefore still requires odd temporal digits at
  both anchors. For shifts of1..45 bits all temporal digits are even;
  for46 bits only the single intrinsic dummy spill can be odd. The two
  anchors cannot both be supplied. The unique1101 support difference then
  forces a whole-B-cell temporal shift.
- Every aligned position0..1096 has total raw contribution at most18;
  adding incoming12 remains below rho. This protects all19 ordinary copy
  predecessors. Complementing both ends preserves the recovered equalities.
- The clause predecessor totals are A_adj and A_adj+2^44*x_3296, with
  `A_adj<=6*2^44-1024`. The larger bound plus12 is below rho. Thus both
  clauses have incoming carry0, although each occupied clause emits carry1.
- The padding-reset totals are c_0*x_2195 at7690 and c_0*x_3296 at8791.
  They are at most2^44; adding12 remains below rho. The ensuing zero bands
  7691..7695 and8792..8806 contain no raw contributions, so no carry enters
  the padding or the next B-cell's origin.

These are full predecessor identities, not simulations of particular
canonical tableaux. They cover arbitrary source witnesses for soundness
and every simultaneous canonical low-dummy subset for completeness.

## Padding, source masks and strict slack

The replacement padding is

    (rho-1) rho^8792 G_15(rho)
    +(rho-1) rho^7691 G_3(rho)
    +(2^28-4) rho^7694.

It uses15*47+3*47+26=872 bits, all in the proven zero bands. The two
clause fields retain46 tested bits each. Together with copy, anchor and
origin tests, the total native high-mask population is still986. The low
mask population is d-986 for d=47*8807. Both origin residues and all scalar
port boxes were checked from the full integers.

The reset tail still gives0<F<q/rho^15 and0<C<q/rho^5510 under every
simultaneous safe low-dummy change. Consequently2C+F<q/3. The actual-rank
population identity depends on these masks and their populations, not on
the population of uncomplemented labels. It therefore still gives
pc(R)=3dN+2 and R=3 modulo4 for the actual defining rank.

## Controller and actual-rank completeness

The new fixed controller is lambda=1,012,691>d=413,929. Its primality was
independently checked by trial division through its square root. The exact
orders are ord_47(B)=23 and ord_8807(B)=4403; their least common multiple
is101269 and divides lambda-1=1012690. The independent arithmetic check gives:

| modulus | B | K0 | 1+B K0+B^2 |
|---:|---:|---:|---:|
|47|12|5|17|
|8807|2677|4079|5042|
|1012691|959313|1005855|834350|

All bracket values and B^2-1 are units at the three primes. The lift is

    B^(lambda-1)=1+282338*lambda modulo lambda^2,

where0<282338<lambda. Thus its valuation is exactly one. Unlike the
radix49 parent, d has no repeated prime factor; no7^2 premise is reused.

Choose fresh independent cofinal width and height powers of lambda. The
parent safe-dummy ordinary-increment proof still applies: all coefficient
residues are below rho, their physical support is unchanged, and the strict
slack holds for every intermediate subset. The changed rank increment is
therefore the same exact algebraic formula with the new K0 and radix.
The certified units make its multiplier invertible modulo the full dN.
The order/lift/CRT argument supplies the required complete orbit and Boolean
subset sums. Thus it tunes the actual rank, rather than selecting an
unrelated target R. The original seam and P66 positive-witness construction
then applies to freshly encoded native words and the coherent new tuple.

## Independent finite evidence and scope

`audit_radix47.py` imports no producing module. It checks all943 tiles,
the label involution, all3297 coefficients by two independent input routes,
the complete four tuple integers against their raw bytes, all mask
populations and port boxes, every copy/anchor/clause/padding basis identity,
the strict numeric carry inequalities, all943 occupied-clause aggregates,
and the new controller's primality, exact fixed-modulus orders, unit values
and valuation-one lift. It passed in normal and optimized Python; explicit
exceptions retain every check under -O.

The finite checker does not replace the unbounded fixed-point, phase,
language, seam, Pell, subset-sum or syntactic-calibration proofs. Those have
been checked above as ordinary proof composition against the retained parent.
The complete assembled author proof was subsequently read end to end and
accepted. Its prior-obstruction attribution was clarified to the explicit
carry93 clause-alias note. No mathematical correction was required.

## Final assembled-proof binding

The reviewed complete author proof is `radix47/radix47_proof.md`, SHA256
`3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224`. The finite arithmetic also independently confirms
`ord_1012691(B)=1012690`: the maximal proper-power residues for prime
divisors2,5,7,17,23,37 are respectively1012690,518329,607777,731320,
122249,706432, all different from1.

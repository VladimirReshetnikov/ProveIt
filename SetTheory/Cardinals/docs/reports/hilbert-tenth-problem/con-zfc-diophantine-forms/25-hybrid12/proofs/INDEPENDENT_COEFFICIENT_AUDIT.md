# Independent audit of the mixed125 coefficient adapter

## Scope and verdict

I compared `mixed125/PROOF.md` with the inherited package-19
`WANG943_COEFFICIENTS.md` and `WANG943_COMPACT_LAYOUT.md`, and inspected the
new materializer and independent byte reconstruction program.

**Verdict: the new coefficient adapter preserves the stated native compiler
interface, relative to the expressly inherited Wang-language, marked periodic
tiling, helical padding, dummy-control, Pell, and K215 calibration theorems.**
No substantive mathematical defect was found in the new mixed-radix clauses,
external population padding, or short-shift geometry. This is an ordinary
mathematical audit, not a new proof-assistant certificate for those inherited
theorems.

The entire four-port tuple must be replaced together. The final high-mask
port is `MF_source = MF_native+B-1`; substituting the unshifted native mask
would invalidate the arithmetic interface.

## 1. Mixed-radix decoding has no circular carry assumption

The native input mask makes all selector, copy, and anchor digits Boolean.
Only the distinguished dummy can use its additional upper bit, and both
dummy clause coefficients vanish. At either clean clause target the lower
ten bits of the clause sum are the selector count `n`. Because

    0 <= n <= 943 < 1024,

there is no carry out of this low block. Every other raw contribution is
divisible by 1024, so higher-field carries cannot change these lower ten
bits. The mask 1022 therefore forces `n=0` or `n=1` before any assertion
about higher fields is needed.

After that conclusion, each two-bit field has raw value at most two:
selected tile bit plus its copy bit, or the selector count plus its anchor
bit. An induction from the low block therefore establishes that no base-4
field carries. Testing its low bit accepts exactly 0 and 2. Thus an empty
cell has no copies or anchors, while an occupied cell has exactly one
selector, copies matching that tile, and all four anchors. The converse is
immediate. This establishes the complete local equivalence, beyond the
finite single-mutation tests.

The common ten-bit occupied label encoding remains unchanged. All edge
labels plus 512 are less than 1024 and have their high bit set. The overlap
tests therefore enforce both edge equality and propagation of occupation
from Start through the cyclic spatial word.

## 2. New geometry still supplies the exact tested fields

The support consists of 989 positions, including the possible upper-dummy
spill at 1064. Its anchors and support span are unchanged from the compact
package-19 geometry. The new clause targets and shifts satisfy:

    (4393-E) mod15625 is disjoint from (5495-E) mod15625;
    ((2195-E) mod15625) intersect ((3296-E) mod15625) = {0}.

These are precisely the two geometric facts needed for a clean clause band
and unique whole-cell anchor alignment. Both include circular residues;
there is no appeal to an unproved interval-separation approximation.

The shortened shift `DR=rho^42` and east-copy bare shift 62 have the intended
effect at spatial targets 1065 through 1074. The other tested target
contributions are unchanged in meaning. At all 22 overlap/anchor targets,
the exact DC, DR, and temporal coefficients agree with the specification;
at both clause targets, the DC coefficient on each native basis position
is exactly its clause coefficient, with no DR contribution. Those basis
identities prove the linear claims for all native assignments, including
the dummy values 0 through 3.

The two-copy bands have gap 1102, absent from `E-E`; the anchors have gap
1101, attained by exactly the intended pair. Every reflected coefficient
exponent is positive. The smallest bare exponent is 30, so no new constant
term interferes with the low-origin convention.

## 3. Binary misalignment remains excluded at b=125

Write a possible temporal binary rotation as `125t+epsilon`, with
`0<=epsilon<125`. For `1<=epsilon<=123`, all rotated low radix digits are
even. For `epsilon=124`, the sole additional possible odd-position type
comes from the upper dummy bit spilling from 1063 to 1064. The support
used by the clean-band test already includes that position.

The two distinct anchor tests at the occupied Start cell require an odd
rotated contribution at each anchor. A nonzero binary remainder cannot
supply both: with remainder at most 123 there are no such odd low digits;
with remainder 124 there is only the one possible spill position modulo
the native cell. Thus the remainder is zero. Once binary alignment is
known, the exact anchor intersection forces `t=0 mod15625`.

The required carry margin still holds. With

    mass = (989+2)(2 sum_e c_e + 6),

`4 mass+8` has 120 bits and is strictly below `rho=2^125`. The six bare
contributions counted by the bound are the four DC shifts, the DR term,
and the temporal term. In particular, an unshifted computational digit
is below rho/4. Even the largest unaligned native dummy contribution
cannot combine with it to create an unaccounted carry; its possible
upper-bit spill is exactly the one already analyzed.

## 4. Moving population filler outside the clauses is legitimate

The new clause masks have 53 bits each. The twenty overlap bits, two
anchor bits, and distinguished low bit contribute 23 more. Thus the
unfilled native output mask has 129 bits, and exactly 860 filler bits
are needed to preserve total population 989.

The proposed filler has `6*123+122=860` bits. Its native positions 9000
through 9006 lie above every possible canonical computational contribution:

    max support(DC times a native cell) = 5495+3296 = 8791,
    max support(DR times a native cell) = 42+3296 = 3338,
    max native temporal support = 3296.

For the canonical completeness witness, dummy tuning makes the temporal
shift an integral number of radix-B cells. The spatial B shift likewise
changes only the cell index. Consequently neither shift can move a native
contribution into positions 9000 through 9006. The carry bound established
above ensures that these support exclusions are actual zero bits, not
merely zero formal coefficients before carrying. They hold for every
allowed dummy choice and every cell of the cyclic word.

Therefore the additional tests never reject a canonical halting witness.
For soundness, satisfying more output-mask tests cannot create a new
spurious tiling; the decoder uses the original low, clause, overlap, and
anchor tests and can discard the extra zero-region tests.

The output mask need not have a single uniform digit mu. The local
decoding argument uses mu only at the two designated clauses. The general
population argument uses total population and the low congruences. The
generic carry/slack estimates can use the maximum mask digit. Here that
maximum is `2^123-1`, and

    2(2^123-1)+4 < 2^125.

Thus replacing the old uniform mask by this heterogeneous collection
satisfies all three distinct uses of the old mask bound.

## 5. Arithmetic interface and actual-rank tuning

The input mask removes 988 permitted native low bits and one extra dummy
upper bit from the all-ones d-bit word. Consequently

    pc(MC)=d-989,
    pc(MF_native)=106+23+860=989.

All individual bit positions are distinct; in particular the filler does
not overlap a clause or other output field. Both masks lie strictly
between 0 and B-1. The low bits remain

    MC=2 mod4, MF_native=4 mod8.

These are the population and low-origin hypotheses of the inherited
shifted inverse-population arithmetic, including its exact two-bit
surplus. In the subsequent twelve-variable arithmetic proof the ordinary
outer bounds use these same mask-size hypotheses, so the new numerical
tuple does not alter that bootstrap.

Both `b=125` and `d=125*15625=5^9` are powers of five. Hence `rho=2 mod5`.
Paired clause contributions cancel modulo five because their exponent gap
is 1102, congruent to 2 modulo 4. The bare shifts give

    DC=2^30+2^62+2^1100+2^2200=0 mod5,
    DR=2^42=4 mod5,
    2DC-DR=1 mod5.

The needed multiplier is therefore a unit. The old proof requires that
unit property, not its former residue 4. The padding changes the initial
packed rank but not the effect of changing a dummy bit; the same Boolean
dummy-control theorem adjusts the actual new rank. The independent
power-of-five width/height padding and the same native dummy positions
remain available. Odd d and odd padded area also preserve the odd-scale
completeness refinements for compatible integer-domain skeletons.

The strong canonical slack bounds remain safe: computational exponents
end at 8791, far below `L=15625`, and native cell coefficients satisfy the
same uniform mass estimate. All unshifted convolutions stay within one
radix-B cell. The cyclic spatial/temporal shifts move whole cells and
introduce no internal padding contamination.

## 6. Reproduction evidence and its limits

I ran `mixed125/verify_independent.py`, which does not import or execute the
coefficient builder. It reconstructed the tuple from the materialized
bytes and returned PASS for:

- all four uncompressed and gzip hashes, populations, and bit lengths;
- 69,230 exact native-basis convolution identities;
- all 943 valid tile clauses and 944 possible selector counts;
- 41,492 single copy/anchor mutations and 44 empty-cell mutations;
- both circular geometric intersections;
- padding disjointness from the complete native output support.

The resulting parameters and sizes are:

    d=1,953,125; beta has 1,953,125 bits;
    K has 1,958,376 bits;
    total four-port uncompressed size=977,220 bytes.

These checks corroborate the fixed finite recipe. They do not simulate the
unknown blank K215 run or decide ZFC consistency. The universal conclusion
is obtained by the local mathematical adapter argument above, followed by
the inherited marked-tiling/blank-halting and finite-refutation equivalences.

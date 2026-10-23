# Independent review of the nonzero-word coefficient adapter

## Verdict and exact scope

**PASS for the new local mathematical adapter and its finite arithmetic
certificate.** This review does not certify the inherited native Pell compiler,
the complete Wang-language argument, or the K215-to-ZFC endpoint anew. The
unchanged 943-tile list has the inherited SHA-256
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
The universal conclusion therefore remains relative to those stated inherited
theorems, by ordinary mathematics formalizable in ZFC, rather than a new
end-to-end proof-assistant result.

The reviewed builder and coefficient files are delivered in
`coefficient_backend/`, with source pin
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
The independent `audit_coefficients.py` imports no builder code. It
reconstructs the four complete integers from the tile-list data and a separately
written recipe, checks the actual binary payloads, and writes
`NONZERO_COEFFICIENTS_INDEPENDENT_AUDIT.json`.

## 1. Removing occupancy bits is sound

The new code of a horizontal label x is x+1 in eight bits; the new code of a
vertical label x is x+1 in nine bits. The actual horizontal maximum is 249 and
the actual vertical maximum is 438, so every code fits and is strictly positive.
The code is injective. West and east use the same code, as do north and south.

The local clause proof has to be ordered correctly. Before decoding any higher
field, the selector count n is between 0 and 943. Every nonconstant clause
contribution is divisible by 1024, so the low ten bits equal n without any
assumption on the upper fields. Disjointness with 1022 forces n=0 or n=1.
Only then may one use the radix-four payload argument: every payload digit is
the sum of at most one selected-tile bit and one copy bit, and is therefore
0, 1, or 2. The low bit of that digit vanishes exactly for equal Boolean bits.
The same argument gives anchor value n.

Thus an empty cell has all edge words zero, whereas an occupied cell has a
nonzero word at every edge. Once native alignment has been recovered, equality
of the complete horizontal words forces the two adjacent cells to have the same
occupancy. Spatial translation is by one cell in a finite cyclic word, so the
presence of Start forces occupation at every cell. Equality of the injective
codes is exactly equality of the original Wang labels. A distinguished high
occupancy bit is unnecessary.

## 2. There is no occupancy/alignment circularity

Global occupancy is not used to establish alignment. The origin condition
already provides selector 0 in the distinguished Start cell. For every proposed
binary rotation, the disjoint clause-hit sets give that cell a clean clause
band. Its clause forces the shared source anchor at 1022 to equal one. The two
tested targets, 1042 and 2107, consequently both require odd temporal digits.

The inherited bit-rotation lemma excludes all nonzero binary remainders:
remainders from 1 through 105 make every temporal native digit even, while
remainder 106 can make only the single upper-dummy spill digit odd. Two
distinct target positions cannot both be supplied by that exceptional position.
The possible spill exponent 1064 is already included in the tested support E.

After bit alignment, the independently checked intersection is

    ((1042-E) mod 6385) intersect ((2107-E) mod 6385) = {0}.

This forces whole-cell alignment. The difference 2107-1042=1065 occurs for
exactly one support pair, (1042,2107), and 6385>2*2107 excludes additional
circular pairs. Only after this stage is the word-based occupancy argument of
Section 1 applied. Sharing the source anchor is harmless because the two tested
temporal positions remain distinct.

## 3. Geometry, padding, and literal coefficients

All 59,902 basis identities hold exactly, not merely modulo a prime. They verify
every current, spatial, and temporal contribution at all label/anchor targets,
and every clause coefficient at both clause targets. The two clause-hit sets
are disjoint modulo 6385. Their gap is 1066 and the anchor difference is 1065;
these are separately tested, rather than conflated.

The largest possible unshifted current-product exponent is
4268+2107=6375. Spatial and temporal contributions are smaller. Consequently
the 870 extra tested bits at radix positions 6376 through 6384 are zero on
every intended aligned witness. The uniform strict carry bound is below
rho=2^107, including the conservative bound for the 105-bit padding digits.
The padding preserves completeness and can simply be ignored for soundness.

The clause mask has population 46; the two clause bands, 19 overlap/anchor
targets, the low bit, and padding give

    2*46+19+1+870 = 982.

The low data mask has population 683195-982. The actual materialized integers
obey the required exact balance and low congruences:

    pc(MC)+pc(MF_native)=683195,
    MC=2 mod 4, MF_native=4 mod 8.

All four ports agree byte for byte with the independently reconstructed values.
Their total raw size is 342269 bytes. The largest port, K, has 688546 bits.
The downstream fourth port is MF_source=MF_native+B-1; substituting the native
mask itself would be incorrect.

## 4. Actual-rank control remains valid

The new integer d=683195 factors as 5*107*1277, and lambda=135257 is prime.
The independently certified orders of B=2^d modulo 5,107,1277,lambda are
4,106,1276,67628 respectively. Their least common multiple modulo d is
67628, which divides k=lambda-1=135256. The exact lifted residue is

    B^k mod lambda^2 = 13998558473,

which is 1 modulo lambda but is not 1 modulo lambda^2. Thus the lifting
valuation is exactly one. All displayed controller unit residues were checked
using the actual, newly materialized DC and DR, not an old tuple.

For N=lambda^n, the first T=N/lambda powers of B^k form exactly the T residues
1+d*lambda*z modulo dN. Indeed, they are all 1 modulo d*lambda, and the
valuation-one lifting identity makes them distinct modulo lambda^n. Their
cardinality is the cardinality of that full residue class. This justifies
the inherited Boolean coverage argument on the new modulus.

To spell out its only delicate choice, normalize a target by B^-2 and subtract
epsilon*B with epsilon in {0,1} so that the remaining target is nonzero modulo
lambda. At least one choice works because B is a unit modulo lambda. Its least
residue a modulo d*lambda is then nonzero, less than d*lambda<T, and coprime
to T. Solve

    a*z0 + a*(a-1)/2 = u mod T.

The a distinct orbit entries whose additive coordinates are
z0,z0+1,...,z0+a-1 sum to the desired residue; the extra position 3 supplies
epsilon*B after normalization. These positions are distinct, and the maximum
orbit position is N-N/lambda-lambda+3. Canonical width w<N/lambda leaves
room for every required translate without wrap or origin interference.

The unit table gives gcd(Gamma,dN)=1 in the unchanged identity

    delta R = -Gamma B^j,
    Gamma = rho^1063 (q^2-1) [1+q(DC+B DR+B^w)].

Therefore the argument adjusts the actual packed rank to R=dw modulo dN.
It does not introduce a fictitious independently selectable rank. The changes
in label coding and support geometry leave this algebraic dummy identity
unchanged; the finite unit certificate is the part that had to be recomputed.

## 5. Remaining proof boundary

The new contribution is a smaller, fully specified admissible coefficient
tuple. It does not by itself change the number of Diophantine witnesses or the
arithmetic circuit. Compatible skeletons must replace all four coefficients
together, and Jones/Sun source-index constants must be rebuilt from the chosen
rebound source polynomial. The finite audit establishes the new adapter's
local hypotheses; it is not a consistency test and does not decide whether
any of the final equations has a zero.

# A smaller coefficient tuple by separating copy positions by parity

This is a new arithmetic-layout adapter for the exact 943-tile Wang language
of package 19 at ProveIt commit `a477d0fc8b6feda53796835564a988015e744d4d`.
It retains that language and its proof, and changes the complete four-port
coefficient tuple. The largest coefficient has 9,766,251 bits rather than
13,201,251 bits. No change to the number of tiles, variables, gates, or the
base `B=2^(5^10)` is claimed by this adapter alone.

## 1. Exact finite definition

The 943 ordered tiles, including Start at selector 0 and the globally
impossible Forbidden tile at selector 1, are exactly those in the inherited
`compiler/WANG943_COEFFICIENTS.md`, Sections 1-2. Their ordered list has hash
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
Each tile is `(west,north,east,south)` with all labels below 512. Set

    A=1024, b=625, rho=2^625, L=15625,
    d=bL=9765625=5^10, B=rho^L.

For `j=0,...,9` use the following native copy exponents:

    e_W(j)=1020+2j, e_N(j)=1000+2j,
    e_E(j)=980+2j,  e_S(j)=960+2j.

Let the native support E be the disjoint union of selectors `0,...,942`,
these forty copy positions, the two dummy positions `1063,1064`, and four
anchors `1095,1096,2195,3296`. Thus `|E|=989` and `max E=3296`.
For a tile with labels `x_t`, `t=0,1,2,3`, define

    c_i=1+sum_(t=0..3,j=0..9) bit_j(x_t+512) A^(1+10t+j)
           +sum_(j=41..44) A^j;
    c_(e_t(j))=A^(1+10t+j);
    c_1095=A^41, c_1096=A^42, c_2195=A^43, c_3296=A^44;
    c_1063=c_1064=0.

Set

    mu=A-2+sum_(j=1..44)(A-3)A^j+2^450(2^78-1),

    DC=rho^40+rho^41+rho^1100+rho^2200
       +sum_(e in E)c_e(rho^(7631-e)+rho^(8733-e)),
    DR=rho,

    MF0=mu(rho^7631+rho^8733)
        +sum_(j=0..9)rho^(1000+2j)
        +sum_(j=0..9)rho^(1021+2j)
        +rho^2195+rho^3296,
    MF_native=MF0+4,
    MC=B-1-sum_(e in E,e!=1)rho^e-2rho^1063.

The complete four arithmetic ports are

    beta=B-1, K=DC+B*DR, MC, MF_source=MF_native+B-1.

All quantities in this section are fixed integers. They are computed from
the literal finite transition table, without waiting for the machine to
halt. In downstream circuit files the port named `MF` means `MF_source`.
None of the new ports except beta may be substituted individually into an
older tuple.

## 2. Why a unit native transport exponent works

The previous layout reserved a large spatial offset to prevent different
copy tests from interfering. Here all copy positions are even, the temporal
copy targets are even, and the spatial copy targets are odd. This makes
`Hc=1`, hence `DR=rho`, sufficient.

Here Hc is a displacement inside one radix-B cell. The multiplier `B*DR`
in K still contains the same factor B, so the horizontal neighbor is still
one whole cell away. No spatial shift of the cyclic word has been replaced
by a single binary bit or a single native radix digit.

For each `j=0,...,9`, at the temporal target `1000+2j`:

* DC's shift 40 contributes exactly the south copy `960+2j`;
* DC's shift 41 would require an odd native position in `[959,977]`, absent
  from E; the other two bare shifts are too large;
* DR's shift 1 would require an odd native position in `[999,1017]`, absent
  from E;
* the rotated native word contributes exactly the north copy `1000+2j`.

At the spatial target `1021+2j`:

* DC's shift 41 contributes exactly the east copy `980+2j`;
* DC's shift 40 would require an odd native position in `[981,999]`, absent
  from E; the other two bare shifts are too large;
* DR's shift 1 contributes exactly the west copy `1020+2j`;
* the rotated native word has no support at the odd target.

The interval of native selectors ends at 942, so it does not invalidate any
of these parity exclusions. The odd native dummy at 1063 and odd anchors
1095 and 2195 are outside these tested intervals.

At anchor target 2195 the four bare shifts see respectively 2155, 2154,
1095 and a negative position. Only 1095 belongs to E. At target 3296 they
see 3256, 3255, 2196 and 1096; only 1096 belongs to E. DR sees 2194 and
3295, both absent. The rotated word sees the two tested anchors themselves.

Every tested target is at most 3296. Every reflected clause exponent is at
least `7631-3296=4335`; multiplying by a native word with nonnegative
exponents cannot contribute at a smaller target. Thus the preceding
identities are exact, including the dummy digits. They give precisely the
same twenty edge-bit matches and two synchronization tests as the older
compiler. Occupancy bits still propagate from Start around the whole cyclic
word, and the edge-bit matches define exactly the original Wang tiling.

## 3. Clause isolation and arbitrary rotations

Write `E=S union {2195,3296}`. Then `max S=1096`. The two clause bands have
gap 1102. No pair within S has that difference. Neither `2195-1102=1093`
nor `3296-1102=2194` belongs to E, and `3296-2195=1101`. Thus

    1102 is not in E-E.

At each clause target 7631 or 8733, each bare shift and DR misses E:
even the smallest candidate `7631-2200=5431` exceeds max E. The opposite
clause band cannot contribute because its gap is absent from E-E. The
coefficient at each tested clause position is therefore exactly
`sum_(e in E)c_e d_e`.

The potential upper-dummy spill position is `1063+1=1064`, already in E.
Consequently the expanded support used for arbitrary binary rotations is
still E. Since `L=15625>2 max E`, the same missing-difference calculation
gives

    {(7631-e) mod L:e in E} intersect
    {(8733-e) mod L:e in E} = empty.

For every rotation, at least one clause band is clean. The inherited
carry-free argument therefore recovers selector, copy and anchor digits.
The occupied ten-bit labels and saturated clause mask are unchanged except
for their locations, so their decoding proof is unchanged.

## 4. Synchronization, including the upper-dummy exception

Write a binary rotation amount as `bt+epsilon`, with `0<=epsilon<b`.
The mass bound below forbids carries. If `1<=epsilon<=b-2`, every rotated
radix digit is even. If `epsilon=b-1`, only the unique upper-dummy spill
can contribute an odd digit. At the marked occupied cell the two tested
anchor positions both require odd digits, so neither nonzero epsilon is
possible. This step is independent of copy-position parity: it uses the
one upper dummy and the two separate tested anchors.

For epsilon zero, the anchor difference is `3296-2195=1101`. No two
members of S have this difference; `2195-1101=1094` is absent, whereas
`3296-1101=2195` is present. Thus the unique support pair of difference
1101 is `(2195,3296)`. There are no additional circular cases because
`L>2 max E`. It follows that

    {(2195-e) mod L:e in E} intersect
    {(3296-e) mod L:e in E} = {0}.

The rotation is therefore aligned to a whole radix-B cell. The original
arbitrary-stride soundness argument now applies; no divisibility or
coprimality assumption on an arbitrary purported solution's stride is added.

## 5. Carry, population and origin bounds

The clause coefficient values are exactly the inherited values, merely
permuted among native exponents. Thus their sum, base-A no-carry inequalities
and all mass estimates are identical. Explicitly,

    mass=(989+2)(2 sum c_e+6),
    threshold=max(4 mass+8,2 mu+4,16).

The mass has 461 bits and threshold has 529 bits, both below `rho=2^625`.
The stronger slack inequalities also remain valid:

    3rho/4+mass <= rho-2,
    rho/2+1+mass <= rho-2.

The largest DC-product exponent is `8733+3296=12029<L`, and the largest
DR-product exponent is only `1+3296=3297<L`. Hence there is no new intercell
spill. Uniform boundedness and the strict canonical raw slack follow by the
same inherited argument, not by an assumption that only tested positions
matter for carries.

The two clause masks contain `2*483=966` bits. The twenty edge tests, two
anchor tests and added low bit contribute 23 more. Their supports are
disjoint, so `popcount(MF_native)=989`. The low mask clears 988 native low
bits (all except selector 1) and one upper dummy bit, so

    popcount(MC)=d-989,
    popcount(MC)+popcount(MF_native)=d.

Every field-mask bit and every cleared data-mask bit lies strictly below
the cell cutoff; neither mask integer has bits at positions d or above.
The low mask MC does have its highest in-cell bit set. Moreover
`0<MC,MF_native<B-1`, `MC=2 mod 4`, and `MF_native=4 mod 8`.

DC has minimum exponent 40 and DR minimum exponent 1, both positive.
Therefore the low-origin field unit still comes only from the temporal
neighbor's selector 0. The canonical unique Start is not its own temporal
neighbor. The compiler's special origin mask test is consequently unchanged.

## 6. Actual-rank adjustment and canonical parity

Because 625 is 1 modulo 4, `rho=2 mod 5`. Paired clause contributions
cancel modulo 5 because their exponent gap 1102 is 2 modulo 4. The bare
terms give

    DC = 2^40+2^41+2^1100+2^2200 = 1+2+1+1 = 0 mod 5,
    DR = 2 mod 5,
    2DC-DR = 3 mod 5.

This is a unit. The inherited dummy change of the actual packed rank has
coefficient

    Gamma=rho^1063(q^2-1)[1+q(DC+B DR+B^w)],

with residue `2 mod 5`, and hence is a unit modulo `dN`, where d and N
are powers of five. The same Boolean subset argument adjusts the actual
rank to the required stride congruence. All dummy effects occur at the same
positive high exponent, preserve tile and overlap assignments, and preserve
the origin and slack conditions just checked. Independent arbitrary large
power-of-five width and height padding is a property of the unchanged tile
language. Completeness is therefore preserved.

The odd-scale completeness identity is unchanged. For `q=2^t`, `M=q^2`,
`S=(C-1)+qF`, and
`Tmask=(MC J+1)+q(MF_native J-1)`, native disjointness gives
`popcount(Tmask)=t+2` and `S AND Tmask=0`. The exact packing identity

    R=(M-1-S)M+(S+Tmask)

therefore gives `popcount(R)=3t+2`. The half-binomial identity then yields
`v_2(Y)=3t`, so `Y=sq^3` has odd positive s. Thus the tuple satisfies the
same compiler hypotheses used in the accompanying twelve-positive and
twenty-four-integer root reductions, including the square-w and odd-i
completeness refinements.

## 7. Exact improvement and verification scope

Since `0<DC<B` and `DR=2^625`, the new K has exactly

    d+625+1 = 9,766,251 bits.

This is the maximum bit length of the four actual ports. The prior compact
Wang943 maximum was 13,201,251 bits. The reduction is 3,435,000 bits
(about 26.02%). Raw payload bytes fall from 5,312,269 to 4,882,894;
deterministic gzip bytes fall from 20,260 to 19,820. Compression sizes are
reported as storage facts, not as coefficient heights.

The new builder checks 69,230 basis identities, all-rotation support facts,
the carry and slack inequalities, populations, and the five-adic unit.
An independent checker imports no builder, reconstructs the support,
clause values and coefficients, and compares all four byte payloads exactly.
The inherited independent language checker verifies 943 ordered tiles and
425 explicitly halting control helices (33,800 local tiles and edge tests).
These finite checks supplement the universal proof above and the inherited
tile-language proof. They do not replace the imported native arithmetic
compiler or the exact K215/ZFC-refutation equivalence, and they are not an
end-to-end Lean/Rocq certificate.

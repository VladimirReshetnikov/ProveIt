# A 4,094-tile binary-copy compiler with B = 2^(5^11)

## Result and trust boundary

This construction replaces all four fixed coefficient ports of the existing blank-input K215 native compiler. It changes neither the six-equation arithmetic interface nor any variable count or degree of an ensuing polynomial. The coefficient base is

B = 2^48828125 = 2^(5^11),

rather than the T4-37075 construction's 2^(5^18). Thus the exact bit length of B−1 drops by a factor of 78,125. The largest coefficient has 56,885,626 bits. Unlike the preceding coefficients, all four are practical to materialize in unsigned binary.

The adapter below is an ordinary mathematical proof, supplemented by exact independent finite checks. It is not a fresh Lean/Rocq kernel proof. It inherits the universal native-mask/Pell compiler, rank-tuning lemma, and K215/ZFC endpoint from the source package. Neither a halting K215 run nor Con(ZFC) is assumed or proved by these finite computations.

Repository source pin: `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, report collection `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`. The detailed inherited T4 bridge is package 11-t4/bridge; the inherited bridge proof and endpoint source excerpts are retained in `sources/t4-bridge/` as read-only evidence. All 430 original K215 transitions are retained, including the movement into halt. The dense transition-table SHA-256 is `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`; its literal JSON projection has SHA-256 `880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`.

## 1. A smaller, still complete local language

Use the same 439 cell codes as the old T4 construction: 0,1 are headless tape bits; 2(q+1)+b is bit b with head state q, for q=0,...,215; and L,Q,R,V,H have codes 434,...,438. The initial phases have payloads (0,no head),(0,state0),(0,no head). State215 is padded by stationary identity transitions.

A tile is (left,center,right,next). Start remains S=(L,Q,R,1). Excluded remains E=(H,0,0,H). The alphabet is E together with the old one-head T4 tiles satisfying the following additional filters. The exact independent implementation is `valid` in `build_coefficients.py`.

1. Both adjacent horizontal pairs obey this relation: two ordinary cells are allowed; initial pairs are LL,LQ,QR,RR; an H cell may abut only H or V; the cells immediately after a V belong to {0,L,H}; those immediately before V belong to {0,R,H}. There are no ordinary/initial mixed pairs. No horizontal triple has V at both ends.
2. At an H center, next is initial; if left is V then next=L, and if right is V then next=R. Initial centers cannot have next=H.
3. At an ordinary center adjacent to V, the other horizontal neighbor is a headless bit and next is either 0 or H. In particular the center is headless0 by condition1.
4. If next=H, every non-V member of the horizontal triple is headless or has halt state215.
5. For every ordinary headed cell q appearing at position j of the horizontal triple, there is an **original, nonpadding** K215 transition into q, with movement m and written bit w, such that either j−m lies outside the triple or the observed cell at position j−m is precisely the headless bit w.

Retain E explicitly even though it fails these filters. It is a tile of the old T4 predicate but has no global extension: its left H has ordinary non-V right neighbor, violating horizontal H propagation at that neighboring center. The native forbidden-selector bit continues to exclude it. The new alphabet is therefore a subset of the old alphabet, with exactly the same harmless selector1.

### Soundness

Every globally valid new tableau is an old T4 tableau. The old overlap reconstruction, arbitrary-stride periodic pullback, nearest-boundary strip extraction, initialization, deterministic simulation, and final-halt argument apply unchanged. No global uniqueness of Start is required.

### Completeness

Suppose K215 halts on blank input. Take its finite run, then pad by stationary halt. Choose the two vertical boundaries with at least three permanently blank cells between each boundary and every cell ever scanned by the head. This is possible because the run is finite; the width can still be enlarged arbitrarily. Horizontal boundary rows, initial L^u Q R^v rows, and these blank collars satisfy filters1–4. The first original transition is nonhalting, so no initial phase needs to be immediately before a horizontal boundary.

For filter5, consider any ordinary headed cell in a genuine noninitial computation row. If its state is not halt, its immediately preceding transition is an original move by ±1. The cell from which the head moved contains exactly the written bit and is now headless. Thus, whenever that source cell occurs in the same triple, the required observed equality holds. For a halted row, use the original transition that first entered halt; the completed machine thereafter changes neither the head nor the tape. Its source cell therefore remains the same headless written bit through all padding rows. This is why filter5 intentionally uses only the 430 original transitions, not the stationary padding transitions. The first ordinary row also has an original predecessor: the initialized Q has exactly the payload of the blank initial head.

At the helical seam, V is independent of time and separates different strips. Its immediate neighbors are blank, initial L/R, or H, so the nine V-centered combinations remain valid. The strengthened blank collar also protects every triple adjacent to V. Hence the old helical extension still gives a valid cyclic word at every sufficiently large independently chosen width and height, with one canonical Start and no E. The stronger filters preserve all width/height choices needed for the five-adic rank adjustment.

### Exact finite count

The canonical ordering is S, E, then all other accepted four-tuples lexicographically. Direct finite enumeration gives 4,094 tiles, materialized as `tiles4094.json`. Its SHA-256 is `d36129e15ecde1704c865d94486c1d485f7edc4a16d311e66a96e30b0daea20b`.

An independent center-class calculation gives: headless0, 1457; headless1, 1484; working heads, 1122; halted heads, 8; initial L,Q,R, 4,1,4; V,9; H,5. The first count includes E. These sum to4094. The independent program uses only incoming movement/write sets and elementary pair counts, not the tile predicate.

## 2. Binary copies instead of one-hot cell copies

Let a=11. Encode each cell symbol s by the nonzero Boolean vector

χ(s) = (bit_0(s),...,bit_8(s),1,0).

The first nine bits injectively encode all 439 symbols. The constant1 coordinate makes occupied cells distinguishable from empty cells. The last zero is a harmless guard, chosen to retain the convenient a=3 modulo4 geometry.

Put k=4094, ell=12, A=4096, and

μ = A−2 + Σ_(j=1)^48 A^j.

For selector i and its tile w_i, define

v_i = 1 + Σ_(j=0)^3 Σ_(t=0)^10 χ(w_i[j])_t A^(1+11j+t) + Σ_(t=1)^4 A^(44+t).

Each copy position for slot j and coordinate t has coefficient A^(1+11j+t). The four anchors have coefficients A^45,...,A^48. The dummy coefficient is zero.

### The native center clause still means exactly one selected tile

Before any restriction, each selector bit and copy/anchor bit is Boolean. The optional upper dummy bit has coefficient zero. The base-A coefficient in the selector-count digit is at most k; every payload/anchor digit is at most k+1=4095<A. Therefore there is no carry between the base-A digits of the clause sum, even before soundness has established occupancy.

The low mask A−2 forbids every bit of the selector count except its least significant bit. Since the count lies in [0,k]⊂[0,A), it forces count0 or count1. Each other masked coordinate is a low parity bit. With count0, parity forces every copy and anchor to0. With count1, the copy bit must equal its selected tile's χ bit, and every anchor is1. This proof is independent of one-hot payload encoding; an arbitrary Boolean nonzero injective code works.

The three spatial/temporal copy groups compare the corresponding Boolean coordinates by parity. Thus they still enforce equality of the entire symbols. A selected tile has occupancy coordinate1 in all four slots, so occupancy propagates to the adjacent cyclic word position. Starting at selector0, every position is occupied. No all-zero code can impersonate an empty neighboring cell.

## 3. Exact coefficient recipe

Set b=625, Lcell=78125, ρ=2^625, and B=ρ^78125.

The native support ℰ consists of:

- selector exponents0,...,4093;
- left copy exponents4182,...,4192;
- center copy exponents4171,...,4181;
- right copy exponents4160,...,4170;
- next copy exponents4138,...,4148;
- dummy exponent4226;
- four anchor exponents4260,4272,4282,8565.

Thus |ℰ|=4143. Coefficients v_e are as defined in Section2. The largest native support exponent is Emax=8565. Define

D_C = ρ^33 + ρ^12903 + ρ^22 + ρ^4293
      + Σ_(e∈ℰ) v_e (ρ^(30034−e) + ρ^(47168−e)),
D_R = ρ^12892,

M_F^0 = μ(ρ^30034+ρ^47168)
        + Σ_(t=0)^10 ρ^(4171+t)
        + Σ_(t=0)^10 [ρ^(12892+4182+t)+ρ^(12892+4171+t)]
        + ρ^4282+ρ^8565
        + Σ_(z=55734)^59722 ρ^z,

M_C = B−1 − Σ_(e∈ℰ, e≠1) ρ^e − 2ρ^4226,
M_F = M_F^0+4.

The four ports passed to the arithmetic skeleton are exactly

β=B−1, K=D_C+B D_R, M_C, M_F^*=M_F+B−1.

Do not substitute native M_F for the shifted fourth port M_F^*. Do not mix any of these with old window-order coefficients.

## 4. Why the compact field geometry is valid

### Exact convolution targets

The shift33 sends next-copy coordinates to center-copy coordinates. Shift12903=12892+11, together with D_R, tests current-center versus right-neighbor-left and current-right versus right-neighbor-center. The two other bare shifts22 and4293 send anchor4260 to4282 and anchor4272 to8565.

There are exactly35 copy/anchor target positions. At each such target the generator checks the full support, not an assumed range: the indicated two bits are the only contributions from D_C times the native center cell, D_R times the spatial neighbor, and the temporal word. This also verifies that the relatively small shift22 lands in an unused gap at every temporal copy target, rather than accidentally hitting selectors or another copy block.

Every copy/anchor target is below30034−8565=21469. Thus no clause-band monomial can hit one. At clause targets30034 and47168, the bare shifts contribute nothing and the other clause band contributes nothing. These finite support equalities exhaust the changed geometry.

### Carry bounds

Let S=Σ_(e∈ℰ) v_e and mass=(|ℰ|+2)(2S+6). Exact manageable integer arithmetic gives

bitlength(4 mass+8)=604, bitlength(μ)=577,

and verifies 4 mass+8<2^625 and 2μ+4<2^625. These are the inherited conservative mass bounds, including the possible upper dummy bit. No final coefficient expansion is needed for this check. The source bits at the dummy may form native radix digit0,1,2,or3, but v_dummy=0; the general mass proof already includes this optional upper bit.

### Population balancing in zero field positions

The original recipe enlarged μ with thousands of unused base-A digits merely to balance the mask populations. Here its population is only59. The old core native field mask would have

2·59+33+2+1 =154

bits. We need4143 bits, so add3989 tests at radix positions55734,...,59722.

For every aligned native cell, every possible D_C product, D_R product, and temporal contribution has radix exponent at most47168+8565=55733. The no-carry bound prevents any carry into the next radix position. This remains true with any legal dummy digit0..3, and in particular after arbitrary free-low-dummy adjustments. Therefore all3989 new tested bits are identically zero in every intended aligned computation. They impose no new completeness condition. Soundness can ignore these extra restrictions and use the old core mask tests.

The new zero fields lie strictly below Lcell, are disjoint from all core mask fields, and have one bit each. Thus

pc(M_F)=154+3989=4143,
pc(M_C)=48828125−4143,
pc(M_F)+pc(M_C)=48828125.

All exponents are positive except the selector support, whose original handling is unchanged. Consequently M_C=2 mod4, M_F=4 mod8, and 0<M_C,M_F<B−1. These are exactly the native shifted-population interface hypotheses. The padding mask is fixed once and for all, not an additional unknown.

### All-rotation synchronization

Under arbitrary binary rotation, the native support, including the only optional spill position4227, is contained in[0,8565]. The two clause bands are separated by17134>2·8565 and have disjoint rotation-hit sets modulo78125. Hence at least one old clause band remains clean under every rotation. Additional zero-mask bits cannot spoil this argument.

Write a bit rotation exponent as625t+ε with0≤ε<625. The inherited mass argument makes all rotated native digits even for1≤ε≤623. For ε=624 at most the one upper-dummy spill can be odd. The two marked anchor tests require two distinct odd rotated digits. Thus ε=0.

For an aligned radix rotation, the two tested anchors are4282 and8565, whose difference4283 exceeds every lower support exponent. In the entire support the only ordered pair with difference4283 is(4282,8565). No wrapped pair occurs because the circumference78125 exceeds twice the support diameter. Therefore the only common shift bringing support to both tested anchor positions is0 modulo78125. The exact set-intersection check independently confirms this. Whole-cell temporal rotation follows without adding a divisibility condition to the arithmetic stride.

## 5. Five-adic rank tuning and the complete compiler contract

Since b is an odd power of5, ρ=2 mod5. The clause-band separation17134 is2 mod4; therefore every paired clause monomial cancels modulo5. The four bare exponents are33,12903,22,4293, giving D_C=1 mod5; D_R=1 mod5. Hence

2D_C−D_R=1 mod5,

which is a unit. The old proof only needs a unit, not its historical value3.

The same chosen helical witness has one Start and arbitrary sufficiently large width w and height H, both powers of5. A free low dummy change in cell j changes the actual packed rank by

−Γ B^j, where Γ=ρ^4226(q²−1)[1+q(D_C+B D_R+B^w)], q=B^N, N=wH.

Because N and w are powers of5, each is1 modulo4, so q and B^w are both2 modulo5 and the bracket is2D_C−D_R modulo5. Thus Γ is invertible modulo dN, d=5^11. The inherited Boolean-subset lemma on the same safe cell indices tunes the actual rank to dw modulo dN. The extra zero mask fields stay zero after every such change, as proved above. The dummy remains at a positive exponent and does not affect the origin unit-radix-digit argument or the canonical single-Start high-mask test. The same mass bound supplies positive raw slack and all subsequent Pell witnesses.

### Canonical parity and square scale, retained for integer-domain lifts

The tableau area N is a power of5 and d=5^11, so t=dN is odd. The canonical Start gives C=1 modulo4: selector0 is set, selector1 is forbidden, and every other allowed contribution is a multiple of4. Also q=0 modulo4, J=1 modulo4, M_C=2 modulo4, and the native M_F=4 modulo8. In the inherited shifted packing, put S=(C−1)+qF, T_C=M_C J+1, T_F=M_F J−1, and Tmask=T_C+qT_F. Thus S=0 modulo4 and Tmask=3 modulo4. The exact packing identity R=(q²−S)(q²−1)+Tmask gives R=3 modulo4. A dummy modification is divisible by4 and preserves these facts. The retained exact population identity is pc(R)=3dN+2, and the same strict bound3q+1<R<q^4 holds.

The fresh canonical main-Pell witness has X=2^R and q=2^t, hence its power-scale coordinate is w_scale=X/q=2^(R−t). Both R and t are odd, and R>t, so R−t is a positive even integer. Therefore w_scale is a positive integer square. The usual odd auxiliary construction is also retained: the main Pell parameter is even, R is odd, c=ψ_A(R) is odd, and the choice m=cR makes ψ_A(cR)/c² odd. Thus both the normalized ordinary multiplier and its Δ-scaled version can be chosen odd. This supplies the exact canonical hypotheses used by the 27-integer-variable and related domain reductions, not merely the raw blank-compiler equivalence.

Conversely the old native soundness proof, using only the core mask tests, decodes selected tiles, symbol overlaps, whole-cell temporal shift, and a marked periodic tableau. Section1 then gives a blank K215 halt. The exact K215 endpoint and the imported finitary ZFC calibration transport this to the same intended ZFC-provable equivalence between positive Diophantine solvability and existence of a ZFC refutation. This is an adapter to those mathematical theorems, not a claim to have independently reproved or kernel-checked them.

## 6. Size and verification

Exact bit lengths are:

- β:48,828,125;
- K:56,885,626;
- M_C:48,828,125;
- M_F^*:48,828,126.

The K formula is b(Lcell+12892)+1, because0<D_C<B. The shifted field port lies strictly between B and2B. Neither top bit of M_C nor β is removed by its low sparse corrections.

`build_coefficients.py` directly constructs the alphabet and verifies support, convolution targets, all-rotation bands and anchors, base-A no-carry conditions, radix carry bounds, the population equation, and the five-adic unit. It also checks48 padded halting-control presentations, containing4428 local windows, including their helical seams and distinguished markers. `independent_count.py` reproduces the exact4094 count without evaluating the tile predicate. Independent finite audit results in `independent_audit.json` include 435,015 exact sparse convolution basis checks. All four coefficients are fully materialized in `expanded/`; its manifest records their exact bit lengths, sizes, SHA-256 hashes, actual bit populations, mask identities, and modular checks. The uncompressed numeric data total25,421,252 bytes.

# Recommended compact instance: B = 2^(5^10)

This supplement strengthens the independently audited 943-tile construction
in `WANG943_COEFFICIENTS.md`. It retains that entire language, finite count,
canonical order, occupied ten-bit labels, saturated clause mask, carry bound,
helical soundness/completeness proof and arithmetic interface. Only the
native anchor positions and transport/band geometry change. The former
`5^11` instance remains a separate fallback, not a mixed coefficient tuple.

The new four actual integers have been materialized. Together they occupy
5,312,269 bytes, or 20,260 bytes in deterministic gzip form. The new beta
has exactly 9,765,625 bits, which is 390,625 times fewer than the latest
T4 beta at the reviewed commit. The new K has 13,201,251 bits.

## 1. Complete replacement recipe

Keep the 943 ordered tiles, A=1024, all forty copy positions, the two
dummy positions 1063,1064, and

    mu = A-2 + sum_(j=1..44) (A-3) A^j + 2^450(2^78-1).

Replace the anchors by

    u1=1095, u2=1096, v1=2195, v2=3296.

The four anchor clause coefficients are A^41,A^42,A^43,A^44 in that order.
Every selector and copy coefficient c_e is as in the fallback; both dummy
coefficients are zero. The native support E still has 989 positions.

Set

    b=625, rho=2^625, Lcell=15625,
    d=9,765,625=5^10, B=rho^Lcell;
    Hc=5497, T1=7631, T2=8733.

Define the following fixed integers:

    DC = rho^30 + rho^5517 + rho^1100 + rho^2200
         + sum_(e in E) c_e(rho^(7631-e)+rho^(8733-e));
    DR = rho^5497;
    MF0 = mu(rho^7631+rho^8733)
          + sum_(j=0..9) rho^(1013+j)
          + sum_(j=0..9) rho^(6520+j)
          + rho^2195 + rho^3296;
    MC = B-1 - sum_(e in E, e != 1) rho^e - 2rho^1063;
    MF_native=MF0+4.

The recommended four arithmetic ports are exactly

    beta=B-1, K=DC+B*DR, MC, MF_source=MF_native+B-1.

As before, MF in a downstream source circuit means MF_source, not MF_native.
All symbols here are fixed by bounded finite definitions; no integer is
chosen by waiting to see whether K215 halts.

## 2. Exact support instead of conservative interval spacing

The earlier sufficient conditions `gap>2Emax` and widely spaced anchors
are not logically necessary. What the proof actually uses is:

1. each tested overlap/anchor target has its specified DC, DR and temporal
   native-basis contributions, with no clause contamination;
2. each clause target has exactly its clause sum and no bare or DR term;
3. the possible rotation-hit sets at the two clause bands are disjoint;
4. the two tested anchors have exactly one simultaneous support alignment;
5. coefficients have no negative exponent, and unshifted products remain
   within one radix-B cell.

The uniform carry bound already sums the masses of BOTH clause bands.
Their convolution supports may overlap away from tested positions without
invalidating any argument. No decoding step tests those unused positions.
The following explicit arithmetic verifies the five needed properties,
without assuming the old stronger interval conditions.

### 2.1 The exact finite support

Write

    S = [0,942] union [983,992] union [1003,1032]
        union {1063,1064,1095,1096};
    E = S union {2195,3296}.

The possible upper-dummy spill exponent is 1064, already in E. Thus the
expanded support E* equals E. Its maximum is 3296, while max S=1096.

### 2.2 Overlap and anchor targets

For each j=0..9:

- At 1013+j, bare shift 30 sees only 983+j (south copy), and the temporal
  native support sees 1013+j (north copy). DR contributes nothing.
- At 6520+j, bare shift 5517 sees only 1003+j (east copy), and DR shift
  5497 sees 1023+j (west copy). The temporal native support contributes
  nothing there.
- At 2195, bare shift 1100 sees only 1095; the temporal anchor is 2195.
- At 3296, bare shift 2200 sees only 1096; the temporal anchor is 3296.

The other bare shifts miss E in each case. For example the potential
unwanted native positions 2165,2196,3266 do not belong to E.

Clause contamination at a target t would require `T1-t` or `T2-t` in E-E.
For the north-copy and anchor targets these positive differences all
exceed 3296. For the spatial targets they are the intervals

    T1-[6520,6529] = [1102,1111];
    T2-[6520,6529] = [2204,2213].

No difference in either interval occurs in E-E. A pair inside S cannot
produce them, since its span is only 1096. Subtracting the first interval
from 2195 yields [1084,1093], absent from S, and from 3296 yields
[2185,2194], absent from E. Subtracting the second interval from 3296
yields [1083,1092], absent from S; subtracting it from 2195 is negative.
This proves target isolation for all native assignments, including dummy
digits 0..3, by linearity.

### 2.3 Clause targets and clean-band rotation

At T1=7631 and T2=8733, every bare shift misses E. The only candidates
not immediately outside the support span are 2114 and 3216, absent from
E. DR would see 2134 and 3236, also absent. A contribution from the
opposite reflected clause band would require a native support difference
of

    T2-T1=1102.

This difference is absent: it exceeds the span of S, while
2195-1102=1093 and 3296-1102=2194 are absent from E. Consequently the
unshifted clause digit at each band is exactly `sum c_e d_e`.

The same calculation proves that `(T1-E*) mod Lcell` and
`(T2-E*) mod Lcell` are disjoint. There is no additional circular case,
since Lcell=15625 exceeds twice the support span. Thus for EVERY binary
rotation, at least one of the two bands is clean. The selector, binary
copy and anchor decoding of the main proof applies unchanged.

### 2.4 Unique anchor synchronization

The anchor difference is `3296-2195=1101`. Again a pair inside S is too
short; 2195-1101=1094 is absent from E, while 3296-1101=2195 is present.
Therefore the unique support pair of that difference is (2195,3296).
The exact circular intersection is

    {(2195-e) mod15625 : e in E}
      intersect {(3296-e) mod15625 : e in E} = {0}.

The two-anchor parity argument first gives binary alignment, including
exclusion of the one upper-dummy spill case; this unique intersection
then gives whole-cell alignment. Hence no new stride assumption is used.

### 2.5 Carries, populations and the unit

The clause coefficients and native support size are unchanged, so the
same 529-bit threshold is dominated by rho=2^625. All reflected exponents
are positive. The largest possible unshifted DC-product exponent is

    T2+max(E)=8733+3296=12029 <15625.

The DR-product exponent is at most 5497+3296=8793. There is no intercell
spill before applying the intended spatial and temporal shifts. The
uniform mass estimate therefore gives the identical no-radix-carry and
positive-slack bounds.

The mask populations remain `pc(MF_native)=989` and `pc(MC)=d-989`,
with MC=2 mod4 and MF_native=4 mod8. The gap1102 is 2 mod4, so paired
clause terms cancel modulo5. The four bare terms give DC=3 mod5 and
DR=2 mod5, whence

    2DC-DR=4 mod5.

This is still a unit, so the actual-rank dummy adjustment and all
canonical completeness arguments remain valid. No other arithmetic,
logical calibration, language or helicity proof has changed.

## 3. Materialization and finite verification

`coefficients_compact/{beta,K,MC,MF_source}.bin` are the actual four
minimal-byte unsigned little-endian integers with no header. Their `.gz`
counterparts decompress exactly to them. They must not be mixed with
the fallback files under `coefficients/`.

| Port | Bits | Bytes | SHA-256 |
|---|---:|---:|---|
| beta | 9,765,625 | 1,220,704 | 40cc309fcb5dd2942c371d18be6d955d472e6b4c3604034b316194037ac16a5d |
| K | 13,201,251 | 1,650,157 | e79f794af9565a7d824beb423bd03ee9ac117811b9b0e3a83ffe18f8a084de99 |
| MC | 9,765,625 | 1,220,704 | 2e3107193f3b376fc3cfffdaa3ef547e6dd8dfdd4548519c0e33b5ffe2f2371d |
| MF_source | 9,765,626 | 1,220,704 | 8851b54fffd93780996de5f8c69315448e1369c3eea142428d2225a5149d1825 |

The new exact-support checker performs 69,230 native-basis convolution
identities, including DC and DR at both clause targets. It verifies the
two modular intersections and all scalar inequalities explicitly. Actual
binary integers are read back for population, congruence, bit-length and
compression-round-trip checks. A separate auditor independently constructs
the same instance and compares the binaries byte-for-byte.

Reproduce after the language builder:

    python -B build_wang943_compact.py
    python -B materialize_wang943_compact.py

The executable imports are only newly authored files in this packet;
upstream programs remain inert. The original 943-language proof and its
425 helical-control checks apply unchanged. This is still an ordinary
mathematical compiler adapter using imported arithmetic and K215 theorems,
not an end-to-end proof-assistant certificate or a consistency claim.

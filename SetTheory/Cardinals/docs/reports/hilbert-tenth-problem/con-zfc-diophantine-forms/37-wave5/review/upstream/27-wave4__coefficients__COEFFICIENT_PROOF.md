# A mixed-radix Wang943 backend with B = 2^(5^9)

## Result, attribution, and precise scope

The complete four-port tuple constructed here has

    d = 1,953,125 = 5^9, B = 2^d,
    beta = B-1, K = DC+B DR, MC, MF_source = MF_native+B-1.

Its four unsigned binary integers occupy 977,220 bytes in total. The largest,
K, has 1,958,376 bits. This improves package19's d=5^10 by a factor of five
and the previous package20/4094 backend's d=5^11 by a factor of 25.
It changes neither the arithmetic skeleton nor any variable count or degree.
This is not a claim that the resulting enormous coefficients are globally minimal.

The tile language, canonical order and exact-support anchor/band geometry
come from package19 (Wang943), pinned to ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. The source collection is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
The three new changes are:

1. One selector-count digit in radix1024 followed by44 Boolean digits in radix4,
   rather than using radix1024 throughout.
2. Population balancing by860 identically-zero high field tests, adapting the
   zero-field idea of package20's 4094 compiler, rather than saturated huge clauses.
3. The exact support permits spatial transport DR=ρ^42, rather than ρ^5497.

All downloaded programs remain inert. `build_mixed.py` is a new construction
using only literal JSON. It independently reconstructs the943 tiles from the
430 literal K215 actions and compares every tile with the pinned source list.
The universal adapter below is ordinary mathematics. Finite computations do
not prove the inherited native/Pell compiler, the literal K215/ZFC endpoint,
or Con(ZFC), and no end-to-end proof-assistant certification is claimed.

## 1. Retained finite language and its semantic contract

A tile is (west,north,east,south). Vertical colors are tape symbols0,1,
head(q,b)=2(q+1)+b for q=0,...,215, and L,Q,R,V,H=434,...,438.
Working states are0,...,214;215 is halt. Horizontal colors are O,HB,PL,PQ,PR,BAD
with codes0,...,5, followed by directed target-state signals. The199 sorted
right-target states have codes6,...,204; the45 left-target states have
codes205,...,249. The exact original action table is retained, including its
write and movement when it first enters halt. Only the two halt self-loops
are padded by stationary motion.

The complete language has430 transition tiles,2 halt loops,2 unchanged tape
bits,398 right-arrival and90 left-arrival tiles,4 finish tiles,4 initialization
tiles,3 reset tiles,9 seam tiles, and1 forbidden tile:943 in total.
The first original action is (0,0)->(write1,right,state93). The initialization
therefore consists of (PL,L,PL,0), Start=(PL,Q,PQ,1),
(PQ,R,PR,head(93,0)), and (PR,R,PR,0). Forbidden=(BAD,0,O,0) is selector1;
Start is selector0; all other tiles are sorted lexicographically.

The language is not merely compared by cardinality. The independent literal
reconstruction equals the complete source ordered list, whose SHA-256 is
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.

For completeness of the semantic adapter, the source argument is as follows.
A marked periodic Wang plane forces V boundaries on both sides of Start:
its PL/PQ/PR initialization chain has no horizontal cycle through Q without
encountering a V seam. The preceding row must be an H reset row. The
initialization performs exactly the first blank-machine action. Between
successive reset rows, directed horizontal signals implement exactly one
literal transition, preserving a unique head; signals cannot cross V.
The next H row can be produced only from bits or halted heads, so the
machine has halted. Unrelated components and extra Starts do not affect this
soundness argument. Conversely, any finite blank halt admits arbitrary
sufficiently large independent strip widths and heights. Two unvisited blank
margin cells beside each boundary prevent signals from reaching the seam.
All nine allowed seam pairs implement the helical extension. Its periods
(w,-1) and (0,h), with N=wh, give a cyclic word with right-neighbor shift-1,
temporal shift-w, exactly one Start, and no Forbidden. Both w,h may be
arbitrarily large powers of5. An arbitrary decoded temporal shift pulls back
to tile[-x-h0*t] on the plane; neither divisibility h0|N nor coprimality is
assumed. These are the entire language properties needed below.

## 2. The exact new finite recipe

Set b=125, ρ=2^125, Lcell=15625, d=b Lcell=5^9, B=ρ^Lcell.
For j=0,...,43 define W_j=1024·4^j=2^(10+2j).
Encode every edge label x by the ten-bit nonzero word x+512. Its last bit
is the occupancy bit; the other nine bits identify the label. Only like
edge ports are ever compared, so horizontal/vertical numeric reuse is harmless.

For slots west,north,east,south use respective native copy offsets
1023,1013,1003,983. There are ten consecutive copy positions at each offset.
Let E be the disjoint union of selector exponents0,...,942; these forty copy
positions; the two dummy exponents1063,1064; and anchors1095,1096,2195,3296.
Then |E|=989. The possible upper-dummy spill position1064 is already in E.

For tile i, with edge labels x_it in slot order t=0,...,3, set

    c_i = 1 + sum_(t=0..3,j=0..9) bit_j(x_it+512) W_(10t+j)
            + W_40+W_41+W_42+W_43.

At copy exponent e_t(j), set c_e=W_(10t+j). At the four anchors in the
listed order, set c_e=W_40,...,W_43. Both dummy coefficients are0. Set

    mu = 1022 + sum_(j=0..43) W_j.

It has97 bits and population53. Define

    DC = ρ^30+ρ^62+ρ^1100+ρ^2200
         + sum_(e in E) c_e (ρ^(7631-e)+ρ^(8733-e)),
    DR = ρ^42,
    MF_native = 4 + mu(ρ^7631+ρ^8733)
                + sum_(j=0..9) ρ^(1013+j)
                + sum_(j=0..9) ρ^(1065+j)
                + ρ^2195+ρ^3296
                + sum_(z=12030..12889) ρ^z,
    MC = B-1 - sum_(e in E,e!=1) ρ^e - 2ρ^1063.

The four downstream ports are exactly

    beta=B-1, K=DC+B DR, MC, MF_source=MF_native+B-1.

The fourth port is ALREADY shifted. Rebind the entire tuple together;
never mix one of these numbers with a source package's other coefficients.
All definitions are bounded finite arithmetic, independent of whether K215 halts.

## 3. Why mixed-radix decoding is valid

The native low mask allows Boolean selectors, copy bits and anchors, and the
same harmless dummy digits as the source. Let n be the number of selected
tiles in one native cell. Before any decoding, 0<=n<=943. Every nonconstant
clause coefficient is a multiple of1024, so the low ten binary bits of the
full clause sum are exactly n. No carry from any higher digit can affect
these low bits. The low mask1022 forbids bits1,...,9 and therefore forces
n=0 or n=1. This first step DOES NOT assume that the high radix4 digits
were carry-free before selector extraction.

Now condition on n=0 or1. Each of the44 payload/anchor radix4 digits is
one selected Boolean tile bit plus one Boolean copy bit, or n plus an
anchor bit. Each sum belongs to{0,1,2}, so there are no radix4 carries.
The corresponding masked low bit permits precisely0 or2. If n=0, every
copy and anchor is0. If n=1, every copy equals its selected tile bit and
every anchor equals1. This proves the same exact cell decoder as the
source, while using far fewer bits. The global rho carry estimate below
is proved BEFORE selector extraction; the two notions of carry are distinct.

Parity at each overlap test then forces the two corresponding Boolean bits
to agree. Occupancy propagates from Start through the entire cyclic word
because the spatial shift is one cell and each occupied horizontal label
has its occupancy bit1. The injective labels give exactly east=neighbor-west
and south=temporal-neighbor-north. This is the unchanged Wang matching contract.

## 4. Exact geometry, with the smaller spatial displacement

The22 overlap/anchor target identities, valid for every native assignment,
are:

- At1013+j, DC's bare shift30 sees precisely983+j, and the temporal
  native contribution is precisely1013+j. DR contributes nothing.
- At1065+j, DC's bare shift62 sees precisely1003+j, and DR's shift42
  sees precisely1023+j. The temporal native contribution is absent.
- At2195, DC sees precisely1095 through shift1100; temporal contribution
  is2195; DR is absent.
- At3296, DC sees precisely1096 through shift2200; temporal contribution
  is3296; DR is absent.

The spatial targets1065,...,1074 are just above the dummy exponents1063,1064
and below the first anchor1095. Their other candidate DC predecessors are
1035,...,1044 under shift30, all absent from E. The temporal targets under
the new shift62 see951,...,960, all absent; under DR they see971,...,980,
all absent. At the two anchor targets the new bare shift62 and DR42 see
only absent positions. The old shifts1100 and2200 contribute exactly as
listed. Reflected clause terms cannot reach any of these targets, since
7631-max(targets)=4335>max(E)=3296.

At each clause target7631 and8733, the bare shifts and DR miss E. The
other clause band cannot contribute because their difference1102 is
absent from E-E. Explicitly, the low set S=E\{2195,3296} has span1096;
2195-1102=1093 and3296-1102=2194 are absent from E. The same observation
makes (7631-E) and (8733-E) disjoint modulo15625. There is no extra circular
case since15625>2·3296. Hence every binary rotation leaves at least one
clean clause band, exactly as required by the source decoder.

The anchor difference1101 occurs in E-E only as3296-2195. A pair within S
is too short;2195-1101=1094 is absent;3296-1101=2195 is present. Therefore

    {(2195-e) mod15625:e in E} intersect
    {(3296-e) mod15625:e in E} = {0}.

The inherited two-anchor parity argument first excludes binary offsets
1,...,b-2, for which all rotated native digits are even, and b-1, for
which only the one upper-dummy spill can be odd. The distinct two tested
anchors require two odd digits. The intersection above then forces the
remaining radix alignment to be a whole-cell shift. No new stride condition
is imposed or assumed. Added zero-field tests only strengthen soundness.

The new generator checks all69,230 full native-basis convolution identities,
not just these interval explanations, including both clause targets. These
are checks of the full numerical coefficient polynomials with actual c_e.

## 5. Uniform carries and the zero-field population balance

Let mass=(989+2)(2 sum_e c_e+6). Direct finite arithmetic gives

    bitlength(mass)=118,
    bitlength(4mass+8)=120 <125,
    bitlength(mu)=97,
    4mass+8 < ρ and 2mu+4 < ρ.

These are the same conservative bounds used by the source. They apply to
all native assignments, including pre-decoding many-selector cells and
all optional dummy values. The possible extra upper-dummy bit is included.
Thus the global no-rho-carry and positive raw-slack arguments transfer.

Every unshifted DC product, DR product and temporal native term has radix
exponent at most8733+3296=12029. (The exact highest term is attained by
the low selector exponent0 in DC and the high anchor3296 in the native cell.)
No carry can reach the next radix position. Consequently all860 tested
radix bits at12030,...,12889 are identically zero in every aligned intended
cell, including after every safe low-dummy adjustment. They impose no new
completeness restriction and may be ignored in soundness. They lie below
Lcell and are disjoint from all original field-mask positions.

The core mask population is2·53+20+2+1=129; the added860 gives989.
MC removes988 distinct native low bits plus the upper bit of dummy1063.
Hence, with pc denoting binary population,

    pc(MF_native)=989, pc(MC)=d-989,
    pc(MC)+pc(MF_native)=d,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B-1.

All these identities are checked on the fully materialized integers, not
merely inferred from symbolic counts. The masks MC and MF_native are NOT
asserted to be mutually disjoint: they constrain different packed objects.
The relevant disjointness is the decoded data S with its corresponding
packed mask Tmask, as explained in Section7.

## 6. Actual-rank tuning and the unchanged arithmetic interface

Since b=125 is an odd power of5, ρ=2 mod5. Clause-band separation1102 is2
modulo4, so each paired clause monomial cancels modulo5, independently of
its changed c_e. Bare exponents30,62,1100,2200 give DC=0 mod5 and DR=4
mod5. Therefore2DC-DR=1 mod5 is a unit.

For the canonical helical word choose arbitrary sufficiently large powers
of5 for width w and height h, and let N=wh. A free low-dummy change in
cell j changes the ACTUAL packed rank by

    -Γ B^j, Γ=ρ^1063(q²-1)[1+q(DC+B DR+B^w)], q=B^N.

Because N,w=1 modulo4, q=B^w=2 modulo5 and the bracket equals
2DC-DR=1 modulo5. Thus Γ is invertible modulo dN. The same Boolean-subset
rank-tuning lemma, on the same safe cells, tunes rank to dw modulo dN.
The zero fields remain zero under every change, as just proved. Dummies
remain at positive exponents, so neither the unit-digit origin argument
nor the canonical single-Start high-mask test changes. All coarse bounds,
strict positive slack, and subsequent native/Pell witnesses are retained.

Conversely the original arithmetic recovery uses the exact native masks,
clean clause, whole-cell synchronization, copy equalities, and marked
periodic language already proved. Therefore any solution of the same
inputless interface decodes a blank K215 halt. Conversely every finite
blank halt produces its canonical positive witnesses. This supplies the
ENTIRE source interface, not merely a raw tiling equivalence or a match
of modular residues. In particular normalized and ordinary source circuits,
including ordinary quartic32, can bind these four ports as one tuple.

## 7. Canonical parity, square scale, odd multiplier, and odd s

Let t=dN, so q=2^t. Both d and N are odd. Canonical Start gives C=1 mod4:
selector0 is present, selector1 forbidden, all other terms multiples of4.
The temporal shift is nonzero, so the native field has its required zero
low-origin test. As q=0 mod4 and J=1 mod4, define

    S=(C-1)+qF,
    Tmask=(MC J+1)+q(MF_native J-1), M=q².

The native mask constraints give S AND Tmask=0, with0<=S,Tmask<M.
In particular their sum remains below M and its population is the sum
of their populations. Replicated blocks do not overlap. Since MC=2 mod4,
adding1 to MC J increases population by1. Since MF_native=4 mod8,
MF_native J has exactly two trailing zero bits, so subtracting1 also
increases population by1. The exact population balance gives

    pc(Tmask)=N pc(MC)+1+N pc(MF_native)+1=t+2.

The exact shifted packing identity is

    R=(M-S)(M-1)+Tmask
     =(M-1-S)M+(S+Tmask).

The first summand is the2t-bit complement of S, placed above the lower
2t-bit block. Therefore pc(R)=2t+pc(Tmask)=3t+2 exactly. This is unaffected
by dummy adjustment because the same masks and population equation apply.
Also S=0 mod4 and Tmask=3 mod4, hence R=3 mod4. The inherited strict
bounds3q+1<R<q^4-2 and all signed restoration bounds remain available.

The canonical main-Pell witness has X=2^R. Thus its scale
w_scale=X/q=2^(R-t) is an integer square: R,t are odd and R>t.
The main Pell parameter A=Y(X+1)+2 is even, c=psi_A(R) is odd, and the
choice m=cR supplies an odd positive normalized multiplier
psi_A(m)/c². The ordinary Delta-scaled counterpart is also odd, since
Delta=A²-1 is odd. These are the old odd-i and square-w promises.

Finally the authentic half-binomial kernel gives
v2(Y)=pc(R)-2=3t. Since Y=s q³, v2(s)=0: s is positive and odd.
Thus package23's odd-scale reduction transfers as well. This last conclusion
uses the exact population and disjointness identities, not merely R's parity.
It is precisely the additional completeness promise needed for the new
integer-domain synthesis. No auxiliary index construction has been weakened.

## 8. Materialized values and reproducibility

Run `python build_mixed.py` to reconstruct the language, exact finite geometry,
scalar bounds and all four actual binary coefficients. They are unsigned,
minimal-width LITTLE-ENDIAN integers, without headers. The manifest records
bit lengths, populations, residues and SHA-256. Native MF is recovered as
MF_source-beta. The byte sizes are244141,244797,244141,244141 in port order.
The total raw977220 bytes should be distinguished from compressed11231 bytes;
compression is not a claim about coefficient height.

The complete source and semantic dependencies are pinned as follows:

- Package19: `compiler/WANG943_COEFFICIENTS.md`,
  `compiler/WANG943_COMPACT_LAYOUT.md`, `compiler/wang943_tiles.json`,
  `audit/WANG943_INDEPENDENT_AUDIT.md`, `integers/COEFFICIENT_TRANSFER.md`.
- Package20: `coefficients/COEFFICIENT_PROOF.md`, especially the identically
  zero high field tests and canonical parity argument (also available in
  the preceding local4094 deliverable).
- Package23: `proofs/ODD_SCALE_27_PROOF.md`, Section5, for the inherited
  half-binomial valuation identity and its exact population application.
- Literal machine: `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`,
  SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
- Endpoint: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
  mirrors the ordinary finitary blank-halts/refutation calibration. The
  claim of ZFC-provability uses that ordinary calibration, not Lean soundness.

All these repository references use the pin stated at the top, except the
inherited historical compiler proofs already cited explicitly by the source
packages. Composing those ordinary, ZFC-formalizable arguments yields the
claimed ZFC-provable equivalence between no solution in the respective
proper domain and Con(ZFC). This construction proves an equivalence, never
Con(ZFC) itself, and does not certify any claimed global optimum.


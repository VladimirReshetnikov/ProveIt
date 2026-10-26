# Reversed selector positions with overlapping bit3 padding

The complete finite probe finds a **59,297-byte** four-port tuple at
A=1004, clause center1515 and prime L=2521. That is10,152 bytes below the
frozen scaled-clause2953 tuple. A simpler alternative retaining A=1005
and its purely local phase proof uses center1516,L2531 and59,533 bytes.
These are finite research checkpoints; neither changes an accepted source
or substitutes for the complete ordinary native/Pell proof.

The useful change is the order of the selector positions. The original
admissible942 sequence already omitted the universally forbidden original
tile1. Keep its Start selector0 fixed and put its selector i at

    pi(0)=0; pi(i)=942-i for1<=i<=941.

Equivalently, the complete original943 indices in new physical order are
`0,942,941,...,2`. This is a bijection onto precisely the same admissible
tiles. The initializer moves to physical14. Physical941 now contains
original tile2=(0,2,7,1), whose complemented South is510, still even.
All colors, seams, Start data and native tile identities are preserved.

The script first authenticates the complete radix55 page and decoder through
the frozen one-anchor7309 verifier. It reconstructs all old943 tiles, checks
the full admissible bijection, checks the entire unreversed3297-entry Phi
array against its frozen hash, then reverses selector coefficients1..941.
It independently compares all942 resulting coefficients with their decoded
tiles. Every label coefficient and all physical support blocks are unchanged.

## Full tuple for the stronger A1004 variant

Write rho=2^47,M'=2^45,L=2521,d=118487,B=rho^L,beta=B-1.
Let Phi_rev be the unscaled Phi with selector positions permuted by pi,
including the original label terms unchanged. The actual clause array is
`c'_e=2[x^e]Phi_rev`. Every coefficient is even, every selector coefficient
is2 modulo2048, every label coefficient is0 modulo2048, and the maximum is
less than M'. The complete recipes are

    K = rho^18 + rho^1004 + rho^(L+9) + 2rho^1515 Phi_rev(1/rho),
    MC = beta - G951(rho) - rho^960 G26(rho) - rho^1004,
    MF_source = beta + 8G917(rho) - 4 + (M'-4)rho^1515
                + rho^960 G9(rho) + rho^987 G8(rho) + rho^1004.

The identity `8G917-4 = 4+8rhoG916` gives origin coefficient4 and exactly
916 later bit3 tests. Thus all origin residues and the978 native mask
population remain unchanged. No negative native field is introduced.
The physical support is0..950,960..985,1004:978 positions, of which976
have nonzero clause coefficients.

The complete unscaled Phi_rev coefficient JSON has SHA256
`536d32acbef01b9c9b6d8cf306a14e51acd40b35e51e860427143c42725dfdd3`.
The doubled array stored in COEFFICIENTS.json has SHA256
`a3145e015691f63261165c2ab7880e915bac0028321f4192104ff0533a739618`.

## Why the clause can move down

At every output field h<=1003, the reflected coefficient index is at least
1515-h>=512. The complete high-index sum is

    T = sum(c'_e,e>=512) = 57463969448796.

This includes every label coefficient and the entire relevant selector tail.
All terms are nonnegative and each index appears at most once in a fixed
field, so T bounds every reflected field before any count decoding. The
probe separately reconstructs every complete field array and confirms that
T is attained at h=1003. Crucially,

    T + 3 + rho/2 + 57 < rho.

The global carry bound57 therefore gives zero outgoing carry throughout
0..1003, even with an arbitrary temporal fractional phase. Every reflection
is even. Marker1004 consequently retains its low-bit parity identity with
zero incoming carry; no zero outgoing carry is required there. Its actual
kernel coefficient combines to `1+c'_511`, with
`c'_511=29687040444418`.

The full raw clause at1515 is the doubled clause expression plus Boolean
x511, and its predecessor1514 is the doubled adjacent expression plus x510.
The exact one-tile adjacent bound is65215009914882; adding the unit and
carry57 stays below rho. Complete coefficient-array comparisons check both
fields and all17 color-copy fields.

The unchanged low clause mask checks `2n+k+tau+b`, for n0..942,k0..57 and
two Boolean contributions tau,b. All218776 combinations are checked; the
16 survivors have n<=1 and low value at most3. The remaining clause bits
decode the exact complemented colors. Both canonical occupied values
M'+2+b pass the full mask.

One smaller center1514 fails this particular unconditional reset envelope:
the tail beginning511 has sum87151009893214, already above rho/2.
The probe records the exact failing local raw field. This is an obstruction
to this bound and placement family, not a native counterexample or a global
optimality claim.

## Padding where reflections are present

The first reflection is now at530, so some of fields1..916 contain reflected
terms. At any padding field h<=916, a physical reflected input e satisfies

    e <= 985-1515+h <=386<942.

It is therefore a selector input. Once the count clause proves at most one
selected tile, at most one reflected term can contribute. Its residue modulo
2048 is0 or2: it can use either a label weight or a selector weight from Phi.
The local bare copy, spatial input and aligned temporal input contribute
at most three additional units. The complete low residue is therefore at
most5 and avoids bit3. The unconditional reset already proved removes
incoming carry. The probe checks all916 actual arrays, their input ranges,
coefficient residues and full residue envelopes.

Bit2 would not follow from this bound: residue4 is allowed by the envelope.
This is recorded as a scoped negative control. The padding stays below the
first color-copy test960; all dummy increments also stay above the padding.
The exact identity8G917-4 retains origin4, so subtracting1 from the native
mask changes only the origin4 to3, without borrowing through later fields.

## Recalibrated global phase exclusion

All978 coarse marker offsets are checked before decoding; all935 fine
support offsets are then partitioned into zero,932 multiple-selector
contradictions, offset20 and offset19. At offset20, physical941 forces the
first South bit to1, whereas its calibrated complemented South510 has low
bit0. At offset19, the nine copy preimages are941,942,...,949, giving

    South_current=(2South_temporal+I(physical_tile_temporal=941)) mod512.

The sole exceptional label is now510. Recomputing all512 graph states gives
the doubling edges `s -> 2s mod512` plus510->509. The latter branch follows

    510,509,506,500,488,464,416,320,128,256,0.

The recorded rank is at most11, strictly decreases on every nonzero edge,
and has maxima at255 and511. Hence the only directed cycle is0. All942
decoded tile transitions and the empty state are included in the graph.
Every finite temporal cell permutation would force every South label0,
contradicting Start510. Allowing an exceptional label511 would create a
nonzero self-loop; the exact calibration matters and is negatively checked.

The last local product is2519, followed by zero field2520. The three complete
safe-dummy degree bounds are2492,986,977. The entire Boolean convolution
maximum7659829036801885 still gives global carry57. Whole-word origin,
mask-population and rank identities are checked for1,2,3 cells with dummy
bits all off and all on; arbitrary-subset completeness remains an ordinary
proof obligation.

## Complete controller and reproducibility

For prime2521, d=47*2521 is odd and squarefree. Exact orders are23 and1260;
all proper-order factors2,3,5,7 of1260 are checked. The common spacing28980
is coprime to d. The auxiliary prime231841=8*28980+1 exceeds d.

| Modulus | B | K | B squared | 1+BK+B squared |
|---:|---:|---:|---:|---:|
|47|28|42|32|34|
|2521|2021|895|421|1660|
|231841|175320|196865|86302|56592|

The auxiliary square-modulus lift residue19327888648 has quotient83367,
so its valuation is exactly1. Every K value agrees through the full scaled
coefficient route, printed factor2 times unscaled Phi_rev, every decoded
tile/label term, and the whole integer. The four complete port sizes are
14811 bytes each for beta,MC,MF_source, and14864 for K, totaling59297.
All four complete byte hashes appear in RESULTS.json.

The local-only alternative uses A1005,C1516,L2531,d118957,raw59533, orders
23 and2530,spacing2530,auxiliary prime121441 and H values5,1136,65968.
Its phase classification uses934 offsets and needs no offset19 graph case.
It is retained as a complete finite comparison, not mixed into the stronger
tuple.

The entire new code delta was self-read. Both normal and optimized Python
reproduce the frozen receipts using explicit requirements, not assertions.
Frozen probe SHA256:
`c436906e7eae3a3260b61b48857e9ff5dddb23af8b5595e54b374d9ce40af206`.
Frozen RESULTS SHA256:
`52d0cb72931260589f80ddecb9e72a74f84fac8a6990a3bf715e3ca48b6c0e75`.

Independent review identified one stale diagnostic in the frozen probe's
whole-mask sample: its bit1 check still says that physical selector1
represents old selector2. Under the recorded reversal it represents original
tile942. The checked bit and all coefficient/source mappings are correct.
The forthcoming proof-bound verifier corrects the message; the frozen probe
and receipt are preserved byte-for-byte.

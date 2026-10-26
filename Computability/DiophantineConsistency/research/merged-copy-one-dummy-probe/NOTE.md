# Reuse an existing label as the fractional dummy spill position

This is a separate finite improvement over the frozen merged-copy4049
probe. Its low dummy at 978 has no dedicated high dummy. The fractional
phase-46 spill lands at 979, which is already the physical east-bit-zero
label. The whole physical support therefore has 979 positions, while
the weighted coefficient support still has 977.

Set `rho=2^47`, `M=2^44`, and use selectors0..942, south943..951,
north961..969, west970..977, east979..986, low dummy978 and zero-weight
Start marker1006. The unchanged complete decoded selector coefficients
and label weights define Phi. The complete kernel is

```
Lambda = rho^1994 + rho^3001
DC = rho^18 + rho^1006 + Lambda*Phi(1/rho)
DR = rho^9
K = DC + rho^(L+9).
```

The shared rho18 occurs once and copies south into north961..969 and
west into tests988..995. Spatial rho9 supplies east at the latter tests.
Every required extraneous predecessor is absent. The marker's bare and
spatial predecessors are988 and997, both absent. First reflection is1008.
The lower and upper clauses have gap1007, with the one foreign upper
predecessor term `c0*x1006`. The bare marker applied to other physical
inputs ends at1992, and applied to itself occurs at2012; the two clauses
and their predecessors are unaffected.

The last product field is4007. Padding is18 full fields4008..4025 and
low28 bits at4026, hence874 bits. The core remains105, giving979 native
tests and complementary MC population `47L-979`. Every full scalar
integer and its population are rebuilt. No former980 population is
reused. Physical position979 is counted once, as a weighted label, and
is explicitly checked as the destination of the dummy spill.

The dummy coefficient remains zero, so clause decoding is unchanged.
Its successor coefficient is now1024. Before interpretation, the exact
whole convolution including an extra two dummy units has maximum
3836048195695509, compared with Boolean maximum3829914518407087.
The complete raw envelope still proves the global carry bound29. After
alignment, the predecessor may contain an additional2048, explicitly
included in both reset estimates. This is the substantive difference
from the previous dedicated-high-dummy proof.

Start's positive south tests962..969 and marker1006 imply either zero
offset or `20<=r<=962`. Offset20 forces tile942 and its impossible south
bit0. Every larger surviving offset forces two distinct selectors in
one decoded cell. The probe enumerates935 support candidates: zero,
933 multiple-selector contradictions, and the calibrated exception20.
Fractional temporal support remains contained in the physical support
because the sole dummy spill lands on979. Safe-dummy increments have
maximum exponents3979,987,978 and satisfy the explicit exponent-plus-one
margin below L.

Marker1005 has a scoped negative local phase test: at offset19, decoded
tile4 with complemented tuple `(255,507,247,511)` reproduces the full
Start south-copy pattern and marker bit using its east bit7. The probe
does not claim that this local pattern extends to a native solution.

The smallest tested admissible prime is `L=4027`, `d=189269`. The exact
base-two and B orders are23 modulo47 and1342 modulo4027, with prime
factors2,11,61 fully checked. The new spacing is30866. Auxiliary prime
`lambda=246929=8*30866+1` exceeds d, with lift quotient184584. The complete
new K gives `H=(18,2634,79912)` modulo47,4027,lambda. Dense polynomial,
direct decoded-tile and whole-integer K computations agree.

The four complete fixed ports require **94,689 raw bytes**,516 fewer
than merged-copy4049 and2,357 fewer than Start-marker1031. The frozen
sources remain unchanged. This packet supplies finite evidence and a
proof lead; a separate complete ordinary proof, independent review and
page/port binding are required before promotion.

```
python research/merged-copy-one-dummy-probe/probe.py --write
python research/merged-copy-one-dummy-probe/probe.py
python -O research/merged-copy-one-dummy-probe/probe.py
```

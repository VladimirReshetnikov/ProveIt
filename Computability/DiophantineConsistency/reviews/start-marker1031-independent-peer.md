# Independent review of marker1031, length4127

Reviewer: `/root/controller_certificate`, 2026-10-25. **PASS within the
stated ordinary-proof boundary.** No unresolved mathematical or finite
verification finding remains. I read the complete 560-line ordinary proof,
whole exploratory and final verifiers, both explanatory notes, and all
numerical/geometry results. I independently checked the new alignment
argument and rebuilt its finite data without importing project code.

## Frozen inputs and reproduction

Paths are relative to `Computability/DiophantineConsistency`.

| File | SHA256 |
| --- | --- |
| `research/start-marker1031-independent/PROOF.md` | `8877bc3c8826d542513c65b0c5b0d453838390777600b5095d339798c56b4a28` |
| `research/start-marker1031-independent/certify.py` | `7cefcd08fa070f63b209fcb05853dea36a01e2aba5165a3abc4e06d7d1c50850` |
| `research/start-marker1031-independent/certificate.json` | `e02fb75e33ee4ae66cbb140a87778c4fdb674b794cd5efa639b14c2ceabb3378` |
| `research/start-marker1031-independent/coefficients.json` | `eed70657080c55394ae5caf87305ee0323584a504b287b17f29d45bac04291eb` |
| `research/start-marker1031-probe/probe.py` | `b78500c48f0c3bcdd7c8cd3d9b11446f576c0bd860a1724d34c8891abe0c4ddc` |
| `research/start-marker1031-probe/RESULTS.json` | `b0fc0265f673f933cce83409d9697588ea1741e441b30fb37aa495903ad2e8a7` |

Both verifiers were read completely before execution. Each of these
read-only commands passed, with no `--write` option:

```text
python3 -B Computability/DiophantineConsistency/research/start-marker1031-probe/probe.py
python3 -B -O Computability/DiophantineConsistency/research/start-marker1031-probe/probe.py
python3 -B Computability/DiophantineConsistency/research/start-marker1031-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/start-marker1031-independent/certify.py
```

The final runs reproduced certificate hash `e02fb75e...` above. The
final verifier authenticates the exact proof before computation and pins
the previously reviewed7309 verifier/decoder dependency before importing
it. All its guards use explicit exceptions and remain active under `-O`.
Long geometry arrays are compared in full before their counts/hashes are
stored. Default mode byte-compares the deterministic JSON outputs.

During the draft read I reported stale1048 and2059/3108 identifiers in
the coefficient domain and tested-field list. The author was already
correcting those during self-review. I reread the corrected sections and
the entire final diff: the frozen proof has1031,2042/3074 consistently,
including predecessors, dummy bounds and the new prime order. These were
resolved transcription findings, not an unresolved premise.

## Full new alignment argument

The clean clause is available before alignment and recovers both
`n<=1` and all34 label bits in every source cell. It does not use a
marker value, occupation, unique Start or any new controller premise.
The first reflected exponent1033 leaves all tested positions974..981
and1031 in the resetting low band. The calibrated Start south color510
has bits1..8 equal to one, so all eight temporal south sources and the
marker source must be odd. The low-band inequality and phase46's sole
possible odd spill exclude every fractional binary phase.

For an integral offset, the marker test gives either zero or22..1031.
The974 test excludes a wrapped preimage, leaving22..974. The proof's
four cases are exhaustive:22..29 hit absent positions952..959 through
target981;30/31 require absent marker preimages1001/1000;32 forces
selector942 and south bit0; every offset33..974 forces two distinct
selectors through targets974/975 in one unwrapped source cell.

The exceptional case is valid because clause decoding precedes it.
The table's final indexed family gives
`t942=(4,437,2,437)`, complemented to `(251,74,253,74)`.
Thus selector942 forces south bit0 to zero while target975 requires it
to be one. There is no reliance on post-alignment edge equality here.

As an independent finite check, I enumerated all4127 offsets from an
explicitly constructed physical set, without importing either verifier.
There are915 support-compatible offsets: zero,913 with multiple selectors,
and exactly32 with source positions942..949 and sole selector942. I also
decoded tile942 directly from its selector coefficient using the fixed
8/9/8/9-bit color layout, obtaining the same tuple and bit contradiction.

The1030 local obstruction is correctly limited. Decoding tile4 directly
from its selector coefficient gives `(0,4,8,0)`, complemented to
`(255,507,247,511)`. At offset31 the nine south-copy preimages942..950
and marker preimage999 give the signature `[0,1,1,1,1,1,1,1,1,1]`, exactly
the required Start south/marker signature. This disproves that particular
local exclusion argument at1030. It is not a full native counterexample,
a polynomial zero or a global lower bound.

## Remaining ordinary proof and finite interfaces

I read every unchanged argument as well as the new alignment section.
The physical marker remains zero-weight and is still required in MC.
Its aligned value is the Start selector in the temporal successor;
the fresh one-Start word has one shifted marker. Safe dummy subsets
preserve it. Occupation propagates from positive complemented colors
through the spatial cycle independently of any all-one-marker premise.

The new clause gap1032 exceeds the physical support range1031.
Gap-minus-one has exactly `(1031,0)`, giving predecessors2041/3073 equal
to `Aadj` and `Aadj+c0*a`. Every bare/spatial/temporal exclusion is
checked, including the17 label copies and marker1031. The predecessor
bound includes selector942-to-label943 and dummy991-to-label992. The
extra 0/2 dummy990 has adjacent coefficient zero. Both resets follow
from `Aadj<=2M-1024` and `3M+29<rho`.

Before interpretation, the bare/spatial extra-dummy outputs end2021 and
its reflected outputs begin2023. This preserves the disjoint extra
allowance and global carry bound29. The exact local convolution maximum,
including extra dummy contributions, is3829914518407087. The verifier
adds the separate spatial maximum3 and temporal bound before checking
the global inequality. All90 geometry checks pass.

The last product field4105 is exactly `c0*a`, with `c0=34876427265<M`.
It resets the top band, so all fields4106..4126 are zero. This proves
the875 padding tests, with18 full fields4106..4123 and29 low bits at4124.
Core105 plus padding875 equals980; MC population is192989. The source
mask shifts by beta once. The resulting strict bounds hold uniformly
for every safe dummy subset, with `F<q/rho` and
`C<q/rho^(4127-1032)`.

The actual binary rank, `pc(R)=3t+2`, origin residue `R=3 mod4`, exact
ordinary dummy increments and controller subset argument remain valid
at the new tuple. Safe-dummy exponents4064,1000,990 satisfy the required
degree-plus-one margins and avoid wrap. I checked the new full-modulus
units, CRT orbit and safe index bounds, then both positive P66 witness
maps, including the strong multiplier bridge and Pell congruences.
The free-port66-operation template and nonzero leading coefficient
`8*beta^92` retain degree157; old and new specialized polynomials are
not claimed equal.

## Exact controller and whole integers

The certificate establishes prime length4127, exact base-two and B
orders23 and2063, primality of2063, coprime spacing47449 and auxiliary
prime `474491=10*47449+1>193969`. The lift is
`64191514936=1+474491*135285`, giving valuation exactly one.

| Modulus | B | K | B squared | H=1+BK+B squared |
| --- | ---: | ---: | ---: | ---: |
| 47 | 37 | 28 | 6 | 9 |
| 4127 | 1600 | 1451 | 1260 | 3487 |
| 474491 | 39160 | 446034 | 425179 | 153928 |

All three K routes agree: dense reciprocal Horner evaluation, full
decoded tile/control expansion and whole-integer reduction. Separately,
I rebuilt all four integers directly from the complete coefficient array
and explicit physical set, checked their scalar boxes and populations,
and used a newly written trial-division check for all required primes,
exact prime orders, coprimality, H residues and the valuation-one lift.
That no-import calculation gives these same minimal unsigned byte hashes:

| Port | Bytes | SHA256 |
| --- | ---: | --- |
| beta | 24247 | `e9921a2dcab070bceda4c414f37d59881aefb7b61c6a0607ebf9d1ac1e2cc3fb` |
| K | 24305 | `f6653f4678958d23505ecb44cfca6a47b5ebe8e419c5a859f2b210880571dd8d` |
| MC | 24247 | `513493c2cc428a23e0a9eb08ee4d3062b974cb670e50c1010b3a3ee474236674` |
| MF_source | 24247 | `6f3e9ba9c490197a1889571afd8db6d542f138c14fb081fe0481c57e6f152063` |

Total97046 saves1173 bytes from4177's98219. Weighted support remains977
while physical support is980. Deleting the physical marker is rejected
by full geometry and by `Whole complementary populations`, despite
leaving every weighted coefficient unchanged.

The proof author is `/root/complemented47_review`; the probe and final
verifier author is `/root/circuit_reduction`; ROOT coordinates acceptance.
This reviewer edited only this separate review. The result remains
relative to the named inherited ordinary arithmetic, complete syntactic
refutation and foundational calibration contracts. No fresh transitive
formal-kernel/internal-ZFC replay, printed-page review, consistency
decision, actual unsolvability or global minimality is asserted here.

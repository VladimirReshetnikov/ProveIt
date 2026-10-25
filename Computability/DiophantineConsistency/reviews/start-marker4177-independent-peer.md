# Independent review of the Start-marker4177 proof and finite certificate

Reviewer: `/root/controller_certificate`, 2026-10-25. Result: **PASS within
the stated ordinary-proof boundary; no blocking mathematical or finite
verification finding.** This review reads all 546 lines of the new proof,
the entire finite verifier and README, and the certificate's full numerical
and geometry results. Both read-only executions below passed after the
source read. No accepted predecessor was changed and no commit was made.

## Exact reviewed inputs

Paths below are relative to `Computability/DiophantineConsistency`.

| File | SHA256 |
| --- | --- |
| `research/start-marker-independent/PROOF.md` | `1db36f130e31087e751b2c83f9988ba4dda34e4f7525d5c9514766238858386e` |
| `research/start-marker-independent/certify.py` | `569d9da678dea56d1b610b2e1c436686e361b19ec66ad6cd2683c59344441067` |
| `research/start-marker-independent/certificate.json` | `b3e1368f3918e8a3371e11aed9746c2369e8770c9aaa2496b4cf797f3b85b8f8` |
| `research/start-marker-independent/coefficients.json` | `eed70657080c55394ae5caf87305ee0323584a504b287b17f29d45bac04291eb` |

The verifier pins the already reviewed one-anchor7309 verifier
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`
before importing its finite decoder/order helpers. That dependency in turn
authenticates the complete retained radix55 page and decoder. The new
ordinary proof explicitly identifies its immediate zero-weight6007 proof
and the complete radix55 language. The unchanged weighted array hash does
not identify physical support: the zero-weight marker moves from 1984 to
1048 while every weighted coefficient remains unchanged.

## Independent mathematical checks

The flag-free clause lemma is usable before alignment or occupation. Its
low nine tested bits imply `n+k` is 0 or 1 because `n+k<=972<1024`.
The other 34 tested bits force the copied label value, yielding empty or
one genuine tile. In the occupied case incoming carry is zero. The marker
is arbitrary Boolean at this stage; no marker premise enters that lemma.

For the full physical set, the first reflected exponent is 1050, above
all three Start tests 974,981,1048. The exact bare/spatial contributions
at these tests are the two calibrated south bits and selector0, each one
in the forced Start cell. The low-band bound
`12+3*rho/4+29<rho` resets every incoming carry. Fractional phases 1..45
are even; phase46 can have an odd dummy spill at only one residue and
cannot satisfy both distinct south tests.

For an integral offset, the marker test makes either `r=0` or
`39<=r<=1048`. A value `r>974` makes the first south preimage wrap above
1048, outside support. Otherwise `974-r` and `981-r` are distinct
selectors in 0..942 of the same temporal cell, contradicting the clause
lemma. This argument needs neither unique Start nor a unique support
difference. I independently checked this sequencing before reading the
final proof and checked the proof's equivalent direct-offset version in
full. The finite enumeration has 906 support-compatible offsets including
zero, and rejects all 905 nonzero offsets by precisely this obstruction.

After alignment the new marker equation is
`a_j=x_(0,j+width)` modulo N. It does not say that all occupied cells have
marker1. The fresh one-Start canonical word consequently has one shifted
marker. This is enough for the low-bit test; occupation still propagates
from positive complemented colors through spatial equality. The converse
explicitly uses this changed marker assignment for every safe-dummy subset.

The complete clause gap1049 exceeds the support range1048. Gap-minus-one
has exactly the pair `(1048,0)`, so the predecessor identities are exactly
`Aadj` and `Aadj+c0*a`. The bound includes both selector942-to-label943
and dummy991-to-label992 adjacencies. The extra 0/2 part of dummy990 has
zero adjacent coefficient. Thus `Aadj<=2M-1024` and the upper predecessor
plus incoming29 is below `3M+29<rho`. The bare marker copy contributes
to neither predecessor nor clause. All 17 label copies, the marker copy,
both clauses and their resets are accounted for.

The pre-interpretation carry bound remains valid with the new single
bare monomial: all Boolean bare/spatial contributions total at most4,
extra-dummy bare outputs precede all its reflected outputs, and a given
reflected coefficient cannot meet both support translates. The extra
allowance is less than2M. Hence the cyclic map preserves carries0..29.
The exact convolution independently supplies a stronger numerical check.

The last product field4156 is `c0*a`, below `M+29<rho`. Every subsequent
field is actually zero. This proves all eighteen full padding fields
4157..4174 and the29 low bits at4175 pass, and resets the next origin.
Core105 plus padding875 equals980; MC has the complementary population
195339 at `d=196319`. The top zero band yields `F<q/rho`, and the physical
support bound yields `C<q/rho^(4177-1049)`, uniformly for every Boolean
safe-dummy subset.

The source mask is shifted by beta exactly once. I checked the actual
rank identity, the populations giving `pc(R)=3t+2`, and the origin
residues giving `R=3 mod4`. Safe increments have local exponent4098,
spatial1000 and temporal990, with the degree-plus-one margins needed to
bound their sum by `q/rho^2`. Safe cell indices prevent wrap; the two
later terms have distinct residues even when they enter the same cell.
The strict representative bound proves the ordinary equality for deltaF
and hence the stated negative Gamma multiple for deltaR.

The controller proof uses the new exact K. CRT and the valuation-one
lift give the full orbit `{1+d*lambda*z}` modulo dN, of size N/lambda.
The extra B^3 summand ensures a nonzero residue modulo lambda; consecutive
orbit coordinates then give the required Boolean subset sum. All selected
indices and their one-cell/width translates are safe. The rank adjustment
therefore supplies the positive transport witness. Both positive P66
witness maps, the strong multiplier bridge, recurrence congruences and
the retained free-port degree157 leading form were read in full. These
are uses of the named inherited ordinary arithmetic and calibration
contracts, not a new transitive formal replay of those contracts.

## Finite reproduction

From the repository root, both commands returned PASS without writes:

```text
python3 -B Computability/DiophantineConsistency/research/start-marker-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/start-marker-independent/certify.py
```

Every guard is an explicit exception, so optimization retains the checks.
Default mode reconstructs and byte-compares both JSON artifacts; only
`--write` materializes them. The deterministic trial-division and full
order tests authenticate primes4177 and224113, orders23 and87, factor
set `{3,29}`, coprime spacing2001, and `224113=112*2001+1>d`.

| Modulus | B | K | B squared | H=1+BK+B squared |
| --- | ---: | ---: | ---: | ---: |
| 47 | 28 | 26 | 32 | 9 |
| 4177 | 1368 | 3388 | 128 | 2620 |
| 224113 | 189170 | 7706 | 45625 | 158694 |

The lift is `43041573990=1+224113*192053`, so its valuation is exactly1.
The dense reciprocal evaluation, direct tile/label expansion and whole
integer reduction agree at all three moduli. All87 geometry checks pass.
The coefficient sum is3829914518407087; the maximum coefficient is
15049678914561. Physical support has980 positions and weighted support
has977. The entire Boolean convolution, with the extra dummy allowance,
has maximum3829914518407087; the verifier adds the separate spatial and
temporal bounds before checking the global carry inequality.

Deleting the physical marker is explicitly rejected by both the geometry
and `Whole complementary populations` obligations. Its weighted
coefficient is zero, so preserving this negative control matters.

| Port | Minimal bytes | SHA256 of unsigned big-endian bytes |
| --- | ---: | --- |
| beta | 24540 | `92421c3219381e9ad46dc9ba566b0b0761daa17e39f7bfaca0c6f25804b20e27` |
| K | 24599 | `902c4d76872aa987fa6bed8e69abfd451b4bd52e66917c3640a72427cd8ac934` |
| MC | 24540 | `f21ecd5300a182de3fd298e211e32faf0aa5ab03f1e9d8255dc7e0cda60d0984` |
| MF_source | 24540 | `615e912c47f907ae79108220bb1260cfb9b6418b754352c5b2f59490a9d53253` |

The total is98219 bytes,43007 below zero-weight6007's141226. This is a
complete four-port integer-size comparison; printed-page measurements
are reviewed separately.

The proof author is `/root/complemented47_review`; the finite implementation
author is `/root/circuit_reduction`. ROOT coordinates acceptance and the
page. This reviewer contributed an independent preliminary alignment
check, then reviewed the frozen complete proof and code without editing
them. This is an ordinary mathematical and executable finite review,
not a new Lean/native-compiler/internal-ZFC run, a consistency decision,
an actual unsolvability proof, or a global minimality claim.

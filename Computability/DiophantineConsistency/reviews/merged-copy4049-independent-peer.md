# Independent review of the shared-copy length4049 tuple

Reviewer: `/root/controller_certificate`, 2026-10-25. **PASS within the
stated ordinary-proof boundary; no unresolved mathematical or finite
verification finding.** I read the entire ordinary proof, exploratory
probe, final verifier, explanatory documents and numerical/geometry
results before running code. I separately reconstructed the changed
coefficient layout, copy identities, phase partition and whole constants
without importing project modules.

## Exact frozen inputs

Paths are relative to `Computability/DiophantineConsistency`.

| File | SHA256 |
| --- | --- |
| `research/merged-copy-independent/PROOF.md` | `43fb060f197f352ed4b1fe9870ca8fa8a7a1f9a4cfae1967882981767167d64e` |
| `research/merged-copy-independent/certify.py` | `0e1768e6e22373b0717f149994b62e24324909f0ad4843de217f96a16248f5b0` |
| `research/merged-copy-independent/certificate.json` | `6c575be486c16145c92d278086fcf3e7ab08342628b1070392b98bff73e672b3` |
| `research/merged-copy-independent/coefficients.json` | `d5ee3e581324dc89adbf709232f86735482bcd23c27a74dc365542790a1f3456` |
| `research/merged-copy-probe/probe.py` | `6edc1eac81e79d1535df7ec8e8b682d5bfff0d6da0a5db84389c26fb49903918` |
| `research/merged-copy-probe/RESULTS.json` | `f1d2d8f7c1bc8146eaf9b4afe8490b9c1dcb2e6a83174f163145909611105a49` |

The final verifier pins the exact ordinary proof and the previously
reviewed7309 decoder/helper dependency before importing it. The latter
authenticates the complete finite language. Default mode recomputes and
byte-compares both JSON artifacts; only `--write` writes them. Explicit
exceptions retain all checks under optimization. These four commands
passed without writes:

```text
python3 -B Computability/DiophantineConsistency/research/merged-copy-probe/probe.py
python3 -B -O Computability/DiophantineConsistency/research/merged-copy-probe/probe.py
python3 -B Computability/DiophantineConsistency/research/merged-copy-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/merged-copy-independent/certify.py
```

## The shared term and complete local geometry

The changed blocks are S943..951, N961..969, W972..979, E981..988,
dummies970/971 and marker1008. Their weights retain exactly the original
34-bit packing. I rebuilt every moved coefficient from the retained943
selector entries and four explicit power-of-two blocks and compared the
entire3297-slot array. Weighted support is977; physical support is980.
The marker and both dummies remain physical despite their zero weights.

There is precisely one bare `rho^18`, with coefficient1. The two logical
copy roles do not add two copies of that monomial. Both the dense and
direct modular routes deduplicate the exponent, as does the whole kernel
construction; the final verifier explicitly checks that the only unit
kernel coefficients are at18 and1008. I independently reconstructed the
kernel dictionary and verified every tested contribution: targets961..969
receive current943..951, while990..997 receive current972..979 plus the
spatially shifted981..988. The spatial predecessors952..960 of the north
tests and the temporal positions990..997 are absent. Marker1008 receives
only selector0 before temporal addition. Its other possible predecessors
990 and999 are absent. Reflection starts at1010, above every copy test.

The clauses1998/3007 have gap1009, exceeding the full support range1008.
The predecessor gap-minus-one has exactly `(1008,0)`. Thus predecessors
1997/3006 are precisely `Aadj` and `Aadj+c0*a`, with no hidden bare or
spatial term. The marker monomial's low inputs end1996 and its own marker
product is2016, away from these clauses and predecessors. The ordinary
bound correctly includes selector942-to-label943 and dummy971-to-label972.
The extra0/2 part at970 has adjacent coefficient zero. Both predecessors
therefore reset by `Aadj<=2M-1024` and `3M+29<rho`.

## Carry, alignment and every native mask

The pre-decoding reflected bound remains the complete coefficient sum.
There are now only two bare terms plus one spatial term, so the Boolean
unit allowance is3. Extra-dummy outputs988,1978,979 are distinct and end
before its reflected outputs begin1980. Each reflected coefficient has
at most one predecessor across the two bands. These facts establish
`Uraw<Csum+3+2M` and the global carry bound29. The finite full-convolution
maximum, with the extra dummy included, is3829914518407087; the separate
spatial and temporal allowances preserve the same bound.

The low region0..1009 has only three unit terms, giving the proof's
`9+3*rho/4+29<rho` reset. The verifier conservatively checks the stronger
numerical inequality with12, which implies the stated inequality with9.
The moved low dummy's possible phase46 spill lands at the supported971.
There is still only one odd spill residue, insufficient for the two
distinct Start south tests. All other nonzero fractional phases are even.

Before these phase tests, a clean clause has already recovered at most
one selector and all34 labels in every cell. Start's south bits1..8 force
odd sources at962..969, while its copied selector forces an odd source
at1008. Any nonzero integral offset lies in20..1008; the962 test excludes
wrapping and bounds it by962. At20, selector942 and its south bit0 would
both be1, contrary to its calibrated complemented south74. At21..962,
targets962/963 force two selectors in the same source cell. This uses
neither occupation, known marker values nor post-alignment edge equality.
Independent enumeration confirms934 support candidates: zero,932
multiple-selector exclusions, and the sole calibrated exception20.

The aligned marker still satisfies `a_j=x_(0,j+width)`. Fresh one-Start
words consequently have one shifted marker, preserved by every safe
dummy subset. Spatial color equality propagates occupation independently.
The final product4015 is exactly `c0*a`; it resets carry and makes all
later fields zero. Thus all875 padding tests pass:18 full fields4016..4033
and29 low bits at4034. Core105 plus padding875 equals980, and MC has the
complementary189323 bits. Origin resets, strict F and the new
`C<q/rho^(4049-1009)` bound hold uniformly for all safe subsets.

I read the full actual-rank identity and both positive P66 witness maps.
The source mask shifts by beta once. Populations give `pc(R)=3t+2`,
origin residues give `R=3 mod4`, and safe increments now use exponent970.
Their local/spatial/temporal maxima3977,979,970 have the necessary
degree-plus-one margins and no wrap. The ordinary equality for deltaF
and the stated Gamma multiple for deltaR follow from the strict bounds.
The new controller retains the full-modulus orbit and safe-index subset
construction. Its even order506 causes no issue: the modulus dN remains
odd and the required order divisibility is exactly the stated506.
The strong multiplier bridge, Pell congruences, witness positivity and
retained free-port degree157 leading form were all checked at this scope.

## Numerical certificate and independent reconstruction

All90 geometry checks pass. The finite certificate proves L4049 prime,
d190303, exact base-two/B orders23 and506, and all proper-order tests at
prime factors2,11,23. Since23 divides506, the lcm spacing is506, not
their product. The auxiliary prime is `190763=377*506+1>d`.

| Modulus | B | K | B squared | H=1+BK+B squared |
| --- | ---: | ---: | ---: | ---: |
| 47 | 2 | 38 | 4 | 34 |
| 4049 | 318 | 749 | 3948 | 3240 |
| 190763 | 58910 | 144554 | 27604 | 43425 |

The lift is `12561743551=1+190763*65850`, proving valuation one.
All three complete K routes agree. I independently checked the required
primes by trial division, exact orders at every proper prime quotient,
coprimality, auxiliary progression, H residues and lift from a separately
rebuilt whole K. The complete new raw ports also match independently:

| Port | Bytes | SHA256 |
| --- | ---: | --- |
| beta | 23788 | `0e939f9aa81d78e1536799efbaee787ace37a7e76c1fae30b0f31ae395da4c0a` |
| K | 23841 | `6919cc23600464c5c80262a3f9b68b93ed7dd1f6e945e7b86f73c4acebaaa7cc` |
| MC | 23788 | `5d856922192b8e66cbf10b9f87629df165a4a40643e9002a3e3b331613a5ba28` |
| MF_source | 23788 | `7a25246bf134cd1b95ef6bd2fc50e13b15e9f740d04fa4e11d5e4a02287c8990` |

The total95205 is1841 below4127's97046. These are complete integer
measurements; printed-page and rendering measurements remain separate.

The physical-marker omission control fails both geometry and whole
populations. The marker1007/offset19 local pattern using tile4 is also
correctly retained: its marker source is east bit7 at988, not the prior
layout's west bit. The matching local parity pattern is not claimed to
extend to a full native witness or polynomial zero.

The ordinary proof author is `/root/complemented47_review`, the finite
probe/verifier author is `/root/circuit_reduction`, and ROOT coordinates
acceptance. This reviewer changed only this report. The result is relative
to the named inherited ordinary arithmetic, complete syntactic-refutation
and foundational calibration contracts; it is not a new transitive
formal-kernel/internal-ZFC replay, page review, consistency decision,
actual unsolvability result or global minimum. No commit was made.

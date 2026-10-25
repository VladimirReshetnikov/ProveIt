# Independent review of the interior upper-bit padding probe

Reviewer: `/root/controller_certificate`, 2026-10-25. **PASS as a finite
exploration and conditional padding lemma.** No mathematical obstruction
was found, but this is not acceptance of a new complete ordinary proof or
page. The full new-mask/L4111 proof composition remains to be written and
bound to a certificate before promotion.

Reviewed files, relative to `Computability/DiophantineConsistency`:

| File | SHA256 |
| --- | --- |
| `research/start-marker-padding-probe/probe.py` | `e4d82fb9d0b4738ab91305bc968b7d1a6f21e44bf2220b26956bfb58e3a15e15` |
| `research/start-marker-padding-probe/RESULTS.json` | `380e21aba33213b49e415b2bae799ed127210a4c224d4c7c2dc6b41d6fe21b1d` |
| `research/start-marker-padding-probe/NOTE.md` | `248b08525f709c65bc2aaa34a5f624b058394f0600db0a226870b9d9872c3a7a` |

I read the whole script and note, inspected the receipt's complete
parameter/controller data, and independently recomputed and compared
all125 padding rows. The initial receipt retained obsolete parent
`padding`/`zero_end` metadata; I reported that clarity issue. ROOT removed
those unused keys, and the final frozen versions above were rechecked.
All numerical values and the new padding formula remained unchanged.

Both final read-only commands returned PASS:

```text
python3 -B Computability/DiophantineConsistency/research/start-marker-padding-probe/probe.py
python3 -B -O Computability/DiophantineConsistency/research/start-marker-padding-probe/probe.py
```

The script hashes its already reviewed4177 helper before importing it,
uses explicit exception guards and byte-compares its deterministic receipt.
It does not itself bind the complete A1031 ordinary proof; the note
correctly makes that decoding/alignment/carry result a separate premise.

## Why the finite maximum proves the padding lemma

The proposed padding is

    Z=(rho-2^40)*rho^3981*G_125(rho), rho=2^47.

It tests bits40..46 in fields3981..4105, exactly `125*7=875` bits,
disjoint from every existing core test. After A1031 decoding and alignment,
each cell is empty or has one of943 tiles with its complete34 label bits.
Including the forbidden selector1 is conservative. The marker is allowed
to be independently0/1, low dummy0..3 and high dummy0/1; this includes
every canonical safe-dummy subset and every decoded soundness word.

The script computes the maximum over all944 tile/empty choices, then
adds the exact maxima of the three independent nonnegative dummy/marker
terms and arbitrary incoming carry29. Thus it does not assume zero
incoming carry or independence of different fields. A simultaneous
maximizing word is unnecessary: every row is a uniform pointwise bound.

I independently decoded all943 tuples from their full selector
coefficients and rebuilt their bits without importing project modules.
For these target fields, the lower reflection ends at3073, the largest
bare product at2062 and the spatial product at1041. Aligned temporal
inputs end at1031. Only the upper reflection remains, so with
`r=target-3074` the contribution of a decoded input bit at e is simply
`c[e-r]`, with negative-index coefficients zero. The independent extras
are `c[1031-r]+3*c[990-r]+c[991-r]`.

This separate calculation matches every one of the125 stored rows,
including maximizing-tile tie choices. The maximum occurs at field4011:
tile434 contributes641412341794, independent marker/dummies contribute
120473785349, and carry29 gives761886127172. This is strictly below
`2^40=1099511627776`, so every tested upper bit is zero. In fact each
such field also resets its outgoing carry. The local lemma is proved
for all decoded words and arbitrary allowed carry, rather than only for
a sampled computation or one dummy subset.

## Whole tuple and what remains to compose

The script builds all four full integers for L4111 and verifies scalar
boxes, origin residues, native population980 and MC population192237.
It uses the unchanged DC and physical support, the new B-dependent spatial
term, and the new padding with exactly one source-mask shift. Full
reciprocal, direct tile/control and whole-integer K routes agree.

The finite controller has exact base-two/B orders23 and
`2055=3*5*137`, coprime spacing47265 and auxiliary prime
`567181=12*47265+1>193217`. H residues are33,1979,499814 modulo47,4111
and567181. The auxiliary lift is
`269193744678=1+567181*474617`, with nonzero quotient modulo567181.
All order prime factors and trial-division evidence are included.

For a complete ordinary proof, the required remaining composition is
concrete. Apply the unchanged pre-alignment count/copy/origin reasoning
at the new scalar tuple; L4111 still exceeds all possible local product
exponents and twice the physical support span. Then use the new lemma
for the replaced padding tests. The last product4105 still equals
`c0*marker`, resets carry, and leaves five actual zero fields4106..4110.
This supplies origin and strict-representative bounds; the changed C
bound uses `L-1032`. Safe-dummy exponents4064,1000,990 retain the
degree-plus-one margins. The actual-rank population argument then uses
the unchanged980 mask population, followed by the new controller data
and both complete P66 witness maps. These observations explain why the
composition appears available; they do not replace its requested full
written and independently bound theorem.

The new raw port lengths are24153,24211,24153,24153 bytes for
beta,K,MC,MF_source, totaling96670. That is376 below A1031/L4127's97046.
The literal padding expression grows from29 to37 TeX bytes, equivalently
32 to40 when the common `&+` prefix and comma are included. The other
changed exponents retain their digit lengths. Thus this is an eight-byte
source cost for a376-byte integer saving; no actual rendered-size gain
has been measured. It is a useful tradeoff checkpoint, with no global
Pareto or minimum claim against layouts not yet compared.

ROOT authored the probe and note. This reviewer performed read-only
source/executable review and a separate finite recomputation, and edited
only this report. No accepted source was changed, no commit made, and
no new formal-kernel/internal-ZFC run, consistency decision or actual
unsolvability result is claimed.

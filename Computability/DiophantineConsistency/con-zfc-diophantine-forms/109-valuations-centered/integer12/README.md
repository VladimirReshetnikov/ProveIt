# Prime-three interpolation for Con(ZFC)

This is a complete fixed-coefficient family of three polynomials in twelve
unrestricted integer variables. The primary (pure19) points are:

- 209 live binary arithmetic operations, exact degree2848;
- 215 operations, exact degree2336;
- 216 operations, exact degree2304.

They improve both operation count and degree over the pinned source's
12-integer248/4832 and223/16000 equations. The complete ordinary reduction,
including the specified inherited semantic calibration, appears in PROOF.md.
No global minimality, historical novelty, or newly kernel-checked endpoint is
claimed.

## Reproduce

Python3 standard library only; no external packages are required.

    python3 build.py
    python3 verify.py
    python3 -O verify.py --output CHECKS_OPTIMIZED.json

`build.py` writes six complete DAGs in `equations/`: three optimized pure19
forms and three original31-carrier comparison forms. `verify.py` checks
literal reconstruction, all live gates and input ports, every fixed numeral
hash, exact identities, finite prime-three/intersective fixtures, and exact
finite-field line-degree certificates using the actual fixed coefficients.
Explicit exceptions remain active under `-O`. These finite checks supplement
the unbounded proofs and are not semantic tests of consistency.

`coefficients/BINDING.json` describes the exact whole source34 tuple;
its six compressed integer payloads and regeneration recipe are included.
The immutable parent archive `source_interpolation.zip` contains the original
12-integer construction, its full-residue Pell interpolation theorem, and the
inherited generalized signed-kernel/native/refutation provenance. The actual
source commit and archive digest are in PROVENANCE.json.

The main change is structural: the old main radical has strictly negative
even3-adic order, while constant weights1,3,9,27 separate the remaining roots.
This removes every growing Archimedean weight. The reduced carrier
S=srH^5, the intersective polynomial(x²+3)(x³−19), and the integral auxiliary
center translation give the stated smaller polynomials.

# Twelve unrestricted integers: degree768 at141 operations

`PROOF.md` gives the complete new ordinary existence argument. The
authoritative literal graph is `../norm/equation.json`; its polynomial-
identical cancellation-aware graph and arithmetic checker are in `../norm/`.
All twelve unknowns range over Z, and all six original fixed coefficients
are unchanged. This is not a global minimum claim.

Three compatible changes produce the improvement:

1. Replace the high-degree projection numerator by
   Kred=X(2X-3c)-2, using2K=Kred+HcX.
2. Replace the quintic carrier scale by S=srH. It now forces only
   H|Kred^5, but the fixed huge base and a quantitative Pell growth bound
   force the whole projection product to vanish anyway.
3. Decouple the strong scale to I=rc^2. A new p-adic isometry proves
   auxiliary interpolation modulo every modulus supported on I, allowing
   the required residue modulo sr without changing the strong pair.

An integer center translation n -> n+QV and exact norm cancellation give
the final degree768. The141-operation graph uses88 multiplications,
26 additions and27 subtractions. A conservative companion retaining the
old I=src^2 has degree800 at141 operations and needs no strengthened
interpolation theorem.

Compared with the pinned integral parent, degree falls1456 ->768 at the
same141 operations (47.25%). Compared with the lower-degree rational
parent, degree falls1200 ->768 and operations145 ->141 (36% less degree).
There are other variable/degree/operation tradeoffs; none is erased by
this comparison.

The proof's genuinely new steps received a separate ordinary audit.
`verify_arithmetic.py` independently checks23,375 carrier identities,
4,004 signed projection congruences,77 large-base bounds, a necessary
negative control, leading-coefficient arithmetic and seven pinned Git
blobs. Both standard and optimized Python passed; see CHECKS_*.json.
The companion norm checker additionally verifies the exact complete norm
identity, literal graphs, operation counts and whole coefficient payloads.

Reproduce this packet's checks with:

    python -B verify_arithmetic.py
    python -B -O verify_arithmetic.py

Source commit:
84e16e43092614bae262ca59651cb9d77e31a255

`SOURCE_PINS.json` records immutable paths, repository Git blob hashes and
local SHA-256 hashes. `source/` contains unchanged source proofs and the
coefficient binding. The full six payloads are in `../norm/coefficients/`.

The native/refutation calibration remains the parent's named ordinary
dependency. This packet supplies neither a new Lean endpoint nor a newly
formalized internal-ZFC derivation. Finite tests do not replace any part
of the unbounded proof and do not establish consistency itself.

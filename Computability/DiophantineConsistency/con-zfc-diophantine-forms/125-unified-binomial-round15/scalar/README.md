# Powered coprime saturation in eleven integers

`PROOF.md` gives the complete fixed-polynomial definition, both directions of integer-zero existence, and the exact degree certificate. The same six actual source34 coefficients are supplied under `coefficients/`, including their finite reconstruction recipe. All eleven quantified variables are unrestricted integers.

The substantive change is the compatible combination of selective first-Pell/positivity fusion with a powered scalar carrier. Only H, not H^5, appears in the scalar divisor. The carrier then gives H|K^5; the fixed huge native base and the pre-projection rank estimate turn that weaker divisibility into the original exact main projection. A fixed-strong-pair interpolation theorem for every supported modulus permits I=rc² and S=srH without a circular witness choice. Prime-three separation removes the parity factors used by the eleven-variable predecessor.

The authoritative arithmetic-circuit files, live operation counts, complete algebra checks, and degree proof are in `../norm/`. The independent semantic and literal-register audit is in `../scalar_audit/`. See those directories' current release metadata for the finalized circuit schedule; the semantic polynomial does not depend on equivalent schedule optimizations.

Reproduce the local finite controls with Python 3:

    python -B scalar/verify_semantics.py
    python -B -O scalar/verify_semantics.py --output scalar/SEMANTIC_CHECKS_OPTIMIZED.json
    python -B scalar/verify_coefficients.py
    python -B -O scalar/verify_coefficients.py

Run these commands from the release root containing scalar/. Both scripts use the Python standard library. The coefficient wrapper imports only the complete, reviewed source34 recipe bundled locally; it performs finite arithmetic and does not simulate the seed machine.

The semantic controls cover 720 modular front-end checks with the authentic tuple, 1,170 exact Pell quotient valuation checks, 505 finite intersective moduli, and a genuine fixed strong pair whose auxiliary coordinates attain every residue modulo a supported prime power strictly larger than the corresponding prime power in I. These controls remain active under Python -O. They supplement, and do not replace, the unbounded arguments in PROOF.md.

`SOURCE_PINS.json` authenticates the complete inherited proof dependencies and coefficient payloads. The requested current comparison pin is 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6; inherited mathematical files retain their original archive provenance pins rather than being silently relabeled.

The native/compiler/refutation calibration is inherited from the retained ordinary source theorem. No new end-to-end Lean or internal object-ZFC certificate, proof of consistency, global optimum, or new historical minimum variable count is claimed.

## Additional lower-degree split-carrier tradeoff

`CRT_CARRIER_PROOF.md` gives a separate eleven-integer family of exact degree 416 at 125 operations, or degree 456 at 124 operations without centering. Its literal graphs and exact checks are in `../norm_weak/`. It replaces the cubic Y substitution by Y=qv and recovers the exact cubic scale through the coprime 2q² component of a mixed scalar carrier. The main H component still uses only fifth-power divisibility. This changes the proof order, so the complete revised bootstrap and both existence directions are given separately rather than silently folded into the primary proof.

Additional controls:

    python -B scalar/verify_crt_carrier.py
    python -B -O scalar/verify_crt_carrier.py --output scalar/CRT_CHECKS_OPTIMIZED.json

They check 46,207 monic projection instances, 14,350 coprime carrier instances, and 588 pre-scale realness instances including Y=0 and c=0.

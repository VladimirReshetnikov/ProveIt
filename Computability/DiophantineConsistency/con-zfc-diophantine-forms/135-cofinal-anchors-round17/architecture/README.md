# One semantic Pell anchor with aligned amplification

This component gives three explicit natural-domain quartics, each equivalent
under the retained ordinary C222/ZFC calibration to finite ZFC refutability.
The main new mathematical reductions are a single bounded-error row at the
reused semantic anchor J, and amplification K=x using the already required
largest beta quotient-range index. The final proof tightens the two canonical
beta quotient ranges to u,v<x. It retains the square factorial/product fusion,
self-sized radix, six exact powers, eleven modular digits, and dominant root
modulus N*q^x.

Recommended balanced endpoint: strict_natural229, with 229 variables, 179
quadratic residuals, 9,184 collected quartic terms, height 83,954,634.
Sparse companion: strict_natural230, with 230 variables, 180 residuals,
6,858 quartic terms, height 83,954,472.
Smaller-variable high-height companion: strict_natural228, with 228 variables,
178 residuals, 9,866 quartic terms, height 2,445,412,949,744.

Every variable ranges over N={0,1,2,...}. Each complete residual list defines
P=sum_i R_i^2, and the full collected polynomial is supplied separately.
In JSON, [c,[i,j,...]] means c*z_i*z_j*..., using the ordered zero-based
variable list; an empty list means a constant. All three polynomials have
exact degree four. They share the identical raw semantic graph.

The full ordinary proof is proofs/ONE_ROW_SEMANTIC_ANCHOR_PROOF.md. Inherited
proofs are explicitly labelled and retained for source, modular, CRT and
Pell dependencies; their historical endpoint counts are not new results.
The logical calibration and its evidence boundary are inherited from the
Round16 release and retained by the enclosing research packet. No claim of
consistency, global minimality, or a new end-to-end kernel proof is made.

## Offline audit and byte-identical reconstruction

Python 3.10 or later with its standard library is sufficient. These commands
are read-only on the released endpoints and rebuild only in temporary folders:

    python3 -B verify_architecture.py --rebuild
    python3 -B -O verify_architecture.py --rebuild

The verifier checks all affine exports, dependency pruning, natural-domain
restoration certificates, final quadratic degrees, complete quartic
expansions and exact metrics. Five exporter corruptions per endpoint are
rejected. The isolated rebuild copies only the portable source closure and
three production scripts; it needs no intake directory, network or repository.
All 17 selected equation/coefficient/certificate/source files reconstruct
byte-identically. The separate independent semantic audit binds the new
number-theoretic interfaces; finite checks do not replace the ordinary proof.

To construct new endpoints without touching these files:

    python3 -B build_strict_anchor.py --output NEW229 --support-cap 48
    python3 -B build_strict_anchor.py --output NEW230 --support-cap 32
    python3 -B contract_reordered.py NEW229/raw/equation.json NEW228 --support-cap 32

The last command emits only the 228-variable contracted endpoint and its
restoration certificate. Its fixed priority table is tied to the exact raw
source. Source closure, provenance and selected files are recorded separately.

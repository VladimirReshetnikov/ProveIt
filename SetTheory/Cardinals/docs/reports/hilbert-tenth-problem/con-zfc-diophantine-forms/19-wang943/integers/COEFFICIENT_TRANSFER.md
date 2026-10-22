# Coherent coefficient choices for the new integer circuits

## Deliberate whole-tuple instantiation

The integer circuits were first derived and verified with the original package06 quartet as their baseline mathematical interface. Their retained `coefficient_binding` annotations record that provenance. `COEFFICIENT_BINDINGS.json` explicitly selects the new, independently audited Wang943 quartet for the primary compact delivered instantiation, with the original quartet retained as a separate alternative. This is a deliberate replacement of all four fixed ports, not a mixture of old and new coefficients. No gate or witness changes.

The primary assignments are

    beta or Bm1 = B-1 from ../compiler/coefficients_compact/beta.bin,
    K0 or Kconstant = K from ../compiler/coefficients_compact/K.bin,
    MC = MC from ../compiler/coefficients_compact/MC.bin,
    MF = MF_source from ../compiler/coefficients_compact/MF_source.bin.

Each file is the exact fixed nonnegative integer in unsigned little-endian binary with no header. In particular MF_source is already shifted by B-1; do not use the unshifted native MF. The binding manifest includes exact SHA-256 identities and records the arithmetic-circuit hashes, which remain unchanged from the reviewed baseline descriptions.

## Why the signed extensions transfer

The compiler audit establishes the entire original arithmetic interface for this quartet, rather than only matching mask congruences. The same carry bounds, transport/power recovery, marker synchronization, native acceptance and actual-rank tuning apply. The unchanged arithmetic signed proof requires:

1. q>=16 and weak transport bounds3q+1<R<q⁴-2, E>=q⁴>R+2, a=E+Y>E.
2. Arbitrarily large independent powers-of-five spatial widths and temporal heights in canonical completeness.
3. An odd dyadic cell exponent d, canonical R=3 modulo4, and the same signed-main-root restoration bounds.

For the primary compact Wang943 backend, d=5¹⁰ is odd; the separately retained fallback d=5¹¹ is also odd. The canonical product N of the two five-power extents is odd, hence q=2^(dN) has odd exponent dN. The odd tuned R therefore makes w=2^(R-dN) an integer square. Canonical a=Y(X+1) is even, the Pell base a+2 is even, and c=psi_(a+2)(R) is odd. The strong index m=cR used in package14 again makes the normalized multiplier i=psi_(a+2)(m)/c² a positive odd integer. No extra divisibility condition or new index construction is required.

These are precisely the completeness-side facts used in the26-,27- and28-integer reductions. Their soundness-side weak bounds and signed-gamma argument use the same complete source-port interface, so they transfer unchanged. Consequently each coherent backend separately defines a fixed polynomial with the claimed consistency equivalence. The new Wang943 version has materialized coefficients; the baseline version retains its original enormous finite recipes.

## Proof and finite-evidence boundary

The transfer is supported by the universal compiler argument in `../compiler/WANG943_COEFFICIENTS.md`, its compact-layout supplement `../compiler/WANG943_COMPACT_LAYOUT.md`, and `../audit/WANG943_INDEPENDENT_AUDIT.md`, not by numerical coincidence on toy coefficients. The local integer verifiers test the symbolic skeleton and degree certificates; they do not evaluate the final high-degree polynomial on the full materialized coefficients or purport to find an accepting K215 run.

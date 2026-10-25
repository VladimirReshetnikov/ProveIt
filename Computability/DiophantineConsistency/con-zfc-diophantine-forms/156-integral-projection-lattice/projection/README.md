# Nonunit affine projections with integral restoration

This component supplies three complete ordinary quartics, with exact integer coefficients and unrestricted integer variables. Their old and new integer zero sets are in explicit bijection. The new projection uses an affine equation with coefficient -2 and a different surviving monic row to certify that the rationally restored coordinate is integral.

Read `PROOF.md` for the general theorem and the precise application. `ENDPOINTS.json` records the exact metrics. Every profile includes its original source equation, final residuals, complete expanded polynomial, and certificate.

Run the independent checker with Python 3.10 or later and the standard library:

    python3 -B check.py

To regenerate the exact equations and coefficient arrays from the included source data:

    python3 -B build.py

The checker imports no producer. It verifies every substitution, the essential integrality companion, complete coefficient collection, variable liveness, exact degree and height, and the finite-field full-rank certificate. Three deliberately corrupted controls per profile must be rejected.

Source archive identities: `ConZFC_Shared_Factorial_Error_2026-10-25.zip` and `ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip` in ProveIt `docs/incoming` at commit `7a8da414376a80b90ecf799f37ceb26fb9ac674e`. Each source equation's SHA-256 and exact archive-relative path are recorded in `projection_certificate.json`.

The finite transformation theorem composes with the predecessors' retained C222/ZF/ZFC refutation calibration. The complete inherited unbounded proof closure belongs to those attributed source packages. The new code and derivation are AI-assisted research; the rational-root theorem is standard and no worldwide priority or global minimum is asserted.

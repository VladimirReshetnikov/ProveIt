# Thirteen-integer Jones specialization and independent audit

Main result:13 unrestricted integer variables,1409 binary operations, exact degree226334238192. A14-integer comparison has1420 operations and degree226295141096. Both use the same coherent31-variable quartic coefficient tuple and optimized B4 weights as the companion Sun package, but the Jones ratio proof is independent of Sun2026.

Read FIXED_POLYNOMIAL_CARRY_PROOF.md, SIGNED_B4_PROOF.md, then THIRTEEN_GUARD_PROOF.md. COFINAL_BASE_AUDIT.md resolves the earlier square-slack versus square-base objection using exact source proofs. section.tex is the article inclusion. Full circuits and degree certificates are in generated/.

From the combined release root run:

    python3 signed_audit/build_signed_b4.py
    python3 signed_audit/check_signed_b4.py

The scripts require only Python standard library and expect the sibling sun/sources/data, sun/sources audit utilities, and root_checks/bose_chowla_31_optimized.json. Keep those directories together. The generated circuit metadata uses paths relative to the generated JSON file. All fixed ports are authenticated and all weighted quartic coefficients are reconstructed by the checker. No external network or theorem-prover build is used.

The strengthened completeness estimate is proved for the actual canonical witness, not inferred from finite tests: |C/K−Y|<b/N², combined with cap,b<=N and the integral interval0<g<cap, makes the new Delta positive. Its soundness uses the exact identity cap²[K²−4(C−KY)²]=4Delta+(cap−2g)²K².

All proofs here are ordinary mathematics formalizable in ZFC. Checks are diagnostics and do not prove consistency or replace the inherited native compiler/K215 endpoint. New material is AI-assisted; inherited upstream source notices and licences in the enclosing package remain applicable.

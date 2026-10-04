# Independent adversarial audit

Verdict: PASS for the frozen residue-cell/two-free-evolution-parameter theorem and canonical-quotient affine lift, conditional on the specified source-17/source-18 imports.

Read `AUDIT.md` for the mathematical review and boundaries. `CHECK-RESULTS.json` records the fresh finite tests.

To rerun only the independently written arithmetic checker:

    python check_adversarial.py

The checker uses the Python standard library and SymPy. It executes no upstream programs or saved schedules. It checks arithmetic fixtures, not an implemented CA compiler or every conservative CA rule.

No frozen packet file was edited. No article was written or changed.

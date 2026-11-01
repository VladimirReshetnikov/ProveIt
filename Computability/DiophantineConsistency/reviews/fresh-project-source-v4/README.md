# AQ29 successor snapshot after ZFCinPA source changes

The running project pair uses the v2 frozen snapshot and remains historical after workspace changes. A later v3 snapshot incorporated the changed `PRAWitnessCalculus`. This v4 snapshot additionally incorporates the upstream edits to `ZFCinPA.LStepAnd`, `ZFCinPA.LStepEx` and `ZFCinPA.LStepExT`.

The v4 manifest SHA-256 is `2ab2c1988b8f48dc243c7637be90aebaf73134593ee4b6cfa0d43f1a86526489`; the source-audit tool session 3242 exited 0 with all 1,210 sources tracked and matching the workspace at that observation. `check_delta.py` compares pinned v2, v3 and v4 manifests. The 1,210 module names, declared imports, external imports and order match in all three. Relative to v3, three source hashes changed and their declared reverse closure contains 85 modules. Relative to v2, four source hashes changed and their declared reverse closure contains 142 modules, including the endpoint.

These are source-declared static impact calculations, not a proof that any old objects may be reused or that a Lean compilation succeeds. No v4 build has been launched. A future successor needs fresh currentness checks, provider authentication and explicit object-provenance verification.

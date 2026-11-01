# 32-variable degree-6 model equivalence: focused replay

The literal has 32 variables and 142 live gates; `verify_literal.py` checks every gate against the pinned candidate. `AdaptiveAQ32.shifted_no_zero_iff` proves positive-shift no-zero equivalence with the 33-variable parent in every IΣ₁ model for natural port vectors, with the explicit assumption `(2 : V) ≤ (p 0 : V)`. It derives positive signed D using the actual main-root and supporting residuals. `current_no_zero_iff` discharges the assumption for the exact fixed ports using a checked bound. Both context/literal identities are definitional.

Tool session 66916 actually exited 0 with `MATCHED_PASS 10 rows`. The driver rebuilt ten modules twice over the matched 33-model peer, compared source/object/log/direct-input rows, guarded 160 direct companion paths per run, and checked the reported axioms. The full receipt and logs are included. A separate read-only receipt check rehashed both runs, all 44 axiom reports, 320 present/absent companion paths and direct inputs; its saved audit is not an additional Lean replay.

The replay is focused on this suffix. Transitive project and package ancestry and dynamic imports are inherited; the point-in-time source guards do not establish a fully current-source closure.

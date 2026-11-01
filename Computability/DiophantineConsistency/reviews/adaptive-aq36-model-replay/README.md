# 36-variable degree-6 model equivalence: focused replay

The literal has 36 variables and 148 live gates; `verify_literal.py` checks every gate against the pinned candidate. `AdaptiveAQ36.shifted_no_zero_iff` proves the positive-shift no-zero equivalence with the 40-variable parent in every IΣ₁ model, for any four integer ports whose first port is a nonnegative integer. `AdaptiveAQ36.current_no_zero_iff` discharges that premise for the actual fixed port. The literal/context identity is definitional.

Tool session 37965 actually exited 0 with `MATCHED_PASS 7 rows`. The driver rebuilt seven sources in two separate overlays over the same matched 40-model peer, compared their source/object/log/direct-input rows, checked 90 direct companion paths per run, and checked the reported axioms. The full receipt and logs are included. Root independently performed an unsaved read-only receipt audit of both rows, all 22 axiom reports per run, 180 direct companion guards, the candidate/literal pins, and the observed parent exit; that audit was not an additional Lean replay.

The replay is focused on this suffix. Transitive project and package ancestry and dynamic imports are inherited; the point-in-time source guards do not establish a fully current-source closure.

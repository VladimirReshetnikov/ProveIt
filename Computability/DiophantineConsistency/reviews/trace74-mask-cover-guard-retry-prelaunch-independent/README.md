# Mask-cover retry: scoped prelaunch review

**GO for one coordinated author retry** with source SHA-256 `651bae93180a46a42e8e2abedb1e34ef4043178e9a8daa25bd4d0c3de25d6a1b` and runner SHA-256 `6b510d4d095c2adfaea39bb0b5b8fc25f0169d14bb167823d072c3f97ad85308`. No Lean was run in this review.

Retained attempt01 terminal SHA-256 `dd8c726c44d20c963c9846ece25b149e8266793938eb287f43b8f816bdf78f27` records the failed check, with two occurrences of the `zero_le J` function-application error, an unsolved goal and `sorryAx`. Compared against the retained source snapshot, the retry changes only those two proof arguments to `(by simp : 0<=J)`; statement and all hypotheses remain unchanged. The runner diff changes only its source hash pin. The author reports the first actual tool session 82213 exited 1 and was reaped; that failed result is excluded.

Independently reran the runner's read-only pin/resource preflight and all 15 actual report-policy mutation controls; both passed. The scope and inherited project/package/dynamic ancestry restrictions from `reviews/trace74-mask-cover-guard-prelaunch-independent/` remain. Any successful result is a conditional model lemma, not a derivation from a graph zero, fixed-mask binding, full fixed-port guard or iPRA statement. Capture the actual outer tool exit and perform a separate terminal post-audit.

# Artifact audit: nine-variable author stages 3–5

The fresh `h` overlay has recorded successful stages
`DiscreteOrderedRingFacts`, `ModelArithmetic`, and
`ModelExponentialCongruence`. This packet retains their receipts, frozen
sources, dependency outputs and complete compiler logs, plus the first
warning-rejected attempts and registered baseline files for stages 3 and 4.
The live `.olean` objects remain in `/tmp`. These are intermediate modules;
neither nine-variable endpoint has been built by these three stages.

[`audit.py`](audit.py) compares retained and live sources, receipts and logs;
checks the three output hashes and published hard links; checks all 160, 200
and 120 recorded direct-candidate guards, dependency precedence and
companions, warning-policy guards, and pinned parent guards; and verifies the
complete normalized logs. Stage 3's original and accepted logs contain the
same single `push_neg` deprecation warning; stage 4's contain the same three
such warnings; stage 5 is warning-free. The original rejected and accepted
object hashes also match for stages 3 and 4 **within this same overlay**.
That is not a matched independent replay.

The exact source-bound warning policies are checked against the complete
original and retry logs after replacing only the corresponding source path.
The normal audit exited 0, and optimized Python was rejected. It does not run
Lean, authenticate project-transitive, package-transitive or dynamic-loading
ancestry, or exclude changes between sampled checks. The original `/tmp`
artifacts are required to repeat its live checks.

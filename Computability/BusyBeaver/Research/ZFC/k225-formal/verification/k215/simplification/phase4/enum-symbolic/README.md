# Symbolic execution of the permuted enumerator

The exact upstream `EnumPerm.lean` from `b6c7087477` passes the Lean kernel and the unchanged 215-state endpoint clients. It replaces list-selection scaffolding with seven command-execution lemmas and a small `xrun` simplifier. The module shrinks from 645 to 545 lines. The simplifier builds ordinary proof terms; no native evaluation, new axiom or admission is used.

Twenty-eight operational definitions are unchanged, including command decoding, transitions, block programs and halting. Thirty-six retained public theorem statements are unchanged. The helper `cexec_discard_ax` states its same stack directly as `axStack` instead of expanding it through `pushL` and `axList`. The 19 removed scaffold declarations have no consumers among the production modules using `EnumPerm`; the separate legacy refresh checks the older enumerator namespaces.

[Result](result.json) records five fresh modules (`EnumPerm`, AX, root, seed and endpoint), followed by both unchanged endpoint clients and an independent semantic/API client: 14 standard axiom reports in the three clients, with no audit warnings. The semantic client proves equality with the former literal `execAt` on every input, both general and zero-seed L1 statements, and the existing run-composition contract.

The isolated cache copied the exact completed phase-three 185-module basis. Its objects, logs and source snapshots were bound and rechecked. This is an incremental check of the upstream change, not a new fresh compilation of all 185 modules or the later combined phase-four sources. The combined checkpoint is recorded separately.

[Source comparison](source-review.json), [origin](upstream.json), [typed client](Audit.lean), and the [indexed evidence archive](evidence-index.json) preserve the reviewed draft, bounded runner, raw compiler logs and exact input records. Each compiler call held the shared lock, used one worker and a 120-second/12-GiB cap. The cache and canonical sources were not overwritten.

The archive also retains an optional local run-prefix refactor and its failed first kernel attempt. It offered only one net line of reduction before repairs and was not adopted. An earlier preflight correctly stopped before compilation when canonical EnumPerm had advanced beyond the phase-three source pin; the successor explicitly binds the historical basis and freshly checks the changed target. These failed attempts are not proof evidence for the accepted upstream version.

The symbolic-execution refactor is the incoming author's contribution; drop_contract supplied the independent source comparison, isolated checks and unsuccessful optional prefix experiment. The earlier step-soundness simplification was retained by the upstream merge.

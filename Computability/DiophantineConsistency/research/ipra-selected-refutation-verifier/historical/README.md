# Selected-checker historical paired workflow: prepared, not launched

The independent review found that the initial freezer still hardcoded the
prior product endpoint's five reports instead of this task's single final
report. The freezer now checks the real policy through a shared validation
function; `test_real_policy.py` exercises that production function against the
pinned policy and rejects three mutations. The first control rerun exited 1
because its full-chain toy retained the old report list; after correcting that
fixture and strengthening the real-policy test, all 12 normal and optimized
controls passed. Earlier receipts are retained for history; observed fix-run
outcomes are in `freezer-policy-fix-observations.json`. The corrected workflow
passed a separate [independent review](../../../reviews/ipra-selected-checker-historical-workflow-independent-audit/README.md).

This adapts the reviewed joint-thirteen workflow to rebuild both endpoint chains and the two selected-checker modules against separately copied siblings of the authenticated AQ29 historical parent. The fixed policy has ten additions and sixteen exact diagnostics (8 + 5 + 2 + 1), and SHA-256 `e4361ca7aa1032a2391cbd1cce6bded47a2fa993794050accdda5aa3e36b48c9`. The guarded author manifest is pinned at `dae80b2f3bc452f6138da34e5af026c458c7464bdee1b9a1bb9e0d02ca70a7c2`. The runbook gates launch on the independent workflow review, a separate independent audit of author artifact state `385b40c10de33c60da377b0b84ba22ee2c9103e2a32d8dffc25e84857c26af30`, independently observed audit exits, and the authenticated original matched parent and observed exits. Both independent reviews have passed.

The two duplicated square-sum literal/native files are explicitly selected from their tracked Lean package paths. `check_package_choice.py` compares those clean HEAD and workspace bytes with the pinned guarded author's draft blobs; toy controls reject altered source, path, hash, and optimized execution. The two new checker modules remain selected from their committed draft paths; the planner rejects an unexpected package shadow. Parent, peer, seeds, sources and output roots remain isolated, with frozen source, direct dependency, diagnostic, object, and process gates inherited from the joint-thirteen workflow. The setup itself is not a replay.

`run_controls.py` actually exited 0 in session 79677, with ten toy controls (five normal and five optimized-mode rejection controls) and receipt SHA-256 `32fae76945f4e36bdc1cd2292c7a98ef9b315b49116334d1f110a9f237897318`. The same session had an earlier successful exact author-policy/log preflight, receipt SHA-256 `057535005427fc7be99af6ff7c17d32d3c3b48484c460b0b81c07d92b9c9101e`, and successful package-choice mutation tests. The separately observed tracked package choice exited 0. The synthetic author ancestry gate accepted 35 direct edges and rejected incorrect parent and edge/module counts; its normal exit was 0 and optimized invocation exited 1. These are finite controls, not a paired Lean build.

A manifest-only planner invocation actually exited 0, reporting 1,096 parent modules and ten additions; its result remains at `/tmp/ipra-selected-checker-provisional-plan-20261101.json`, SHA-256 `5520a2681baa358f7d2b15ad0810b6a18ce6e121ebbb6d9bfad4424562e9e69b`. A gzip copy of the exact JSON is retained as `provisional-plan.json.gz` (compressed SHA-256 `ec168d0b1554387d71a37c8e358140a8147c3c9dc6ac861e499c8987ac9084f4`). This provisional survey did not check parent source bytes or workspace drift, and omitted 114 parent rows from its reachable graph; the real freezer and parent gates retain and check all 1,210 parent rows. A full strict plan, freeze and preparation were not run.

The selected checker consumes a common bound for witnesses in the selected encoding. Even a successful historical pair would not establish equivalence with a different independently specified proof verifier, formal PDF semantics, or a current-source replay. The guarded parent's package-transitive, dynamic, transient-mutation and unobserved Foundation-wrapper-exit limitations persist.

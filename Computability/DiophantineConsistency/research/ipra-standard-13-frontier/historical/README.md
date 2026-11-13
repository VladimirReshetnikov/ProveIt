# Joint 13-variable historical paired workflow (prepared, not run)

This adapts the reviewed sibling workflow to eight additions over the matched
1,210-module AQ29 parent. Each sibling must use its own authenticated seeds
and rebuild every addition. The fixed policy contains all 13 diagnostics:
eight for the square-sums endpoint and five for the final product endpoint.
The guarded-author policy/log preflight passed for all eight modules. The task
policy SHA-256 is
`18258bc1c51e59d883688efb2eaf76f9c8f2dfa4d6128582a0d967bedef13b6b`.

The first provisional planner correctly refused two draft sources that were
also present under their package paths. The rejection is preserved in
`shadow-refusal-observation.json`. The policy now explicitly selects those
two tracked package paths; `check_package_choice.py` verifies their clean HEAD
blobs and workspace bytes against the pinned guarded-author draft blobs and
hashes. The original draft-shadow guard remains in the planner. Git-backed toy
controls reject a changed workspace source, a wrong policy path, a mismatched
author hash and optimized Python. These package-path changes and controls
require independent review along with the rest of the workflow.

The independent guarded-author artifact audit has since passed with actual
verifier exit 0. The runbook pins its receipt and terminal observation. The
actual ancestry gate accepts that receipt's 27 direct inputs (including Init)
and rejects 19, 26 and 28 in a separate mutation test. The earlier test based
on the guarded state is retained as pre-audit history.

The updated manifest-only planner actually exited 0 with 1,096 parent modules
and eight additions; it does not authenticate parent bytes or workspace drift.
The real freezer must retain all 1,210 parent rows. The five ordinary fixture
suites, including real Lean paired and full-chain toys, and five optimized-mode
rejection controls also actually passed. All observations and hashes are
recorded; none is a real 13-variable paired replay.

Before any real launch, require a separate independent review of this complete
workflow, including the source-path choice, author audit pins and runbook.
Use stable HEAD through
preparation, capture actual exits, and preserve failed attempts. A matched
historical run would still inherit package-transitive, dynamic and unobserved
Foundation-wrapper-exit limits and would not alone settle the consistency
interpretation or the displayed equation's transcription boundary.

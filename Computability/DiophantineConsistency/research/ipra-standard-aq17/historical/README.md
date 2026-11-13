# AQ17 historical paired-extension workflow (prepared, not run)

This adapts the reviewed current-14 historical sibling workflow to the 44
ordered AQ17 additions over the matched 1,210-module AQ29 parent. Each sibling
must use its own authenticated parent objects and rebuild every addition.
The target is `IPRAStandardAQ17`, with three axiom reports; there are 109 named
reports across 34 addition modules. The pinned task policy is generated from
the guarded AQ17 author manifest, and `policy-preflight.py` checks every name
against all 44 recorded author logs and their guarded state. The policy hash
is `516dff5fdda1544558cb2d3b77987165854cbe53390c7b31f3f221aeae1f75ba`.

The planner's manifest-only survey actually exited 0: 1,209 parent modules and
44 additions were in its declared graph. That survey did not authenticate
parent source bytes or check current workspace drift; the real freezer retains
and verifies all 1,210 parent rows. The checked author-only AQ17 run is not a
matched sibling run.

The adapted controls actually exited 0: five ordinary fixture suites,
including real Lean paired and full-chain tests, and five optimized-Python
rejection controls. The AQ17 policy preflight actually exited 0 and checked
all 109 reports. Receipts preserve the output and input hashes. These controls
are toy evidence, not an AQ17 proof replay. A separate independent review of
the adapted driver, task policy, controls, and [real-run procedure](REAL-RUN.md)
is required before launching it; capture actual process exits and preserve
failed attempts. Use a stable HEAD through preparation.

Any eventual matched run would inherit the historical parent, package and
dynamic ancestry limitations and the missing Foundation wrapper outer exit.
It would not alone establish current-source provenance, a display-to-Lean
identification, or the desired theorem about the selected consistency notion.

# Direct-square 14 historical paired workflow (prepared, not run)

This adapts the reviewed historical sibling workflow to the five ordered
direct-square additions over the matched 1,210-module AQ29 parent. Each
sibling must use its own authenticated parent objects and rebuild all five
additions. The target `IPRAStandardDirect14` emits eight named diagnostics,
all fixed in the task policy. The policy preflight checks those names against
the guarded author manifest, all five author log hashes, and their state. Its
SHA-256 is `2b157860dd840d46972bbadfc808cdc570a59abcefb1ca229df685eb17db0273`.

The manifest-only planner actually exited 0 with 1,099 used parent modules
and five additions. It did not authenticate parent source bytes or check live
workspace drift. A real freezer must retain and verify all 1,210 parent rows.
The guarded author run is not a matched sibling run.

All five ordinary fixture suites actually passed, including real Lean paired
and full-chain toys; all five optimized-Python rejection controls passed.
The author-policy preflight also exited 0. The receipts record input hashes
and exact outputs. These checks are toy and recorded-log evidence, not a
direct14 paired proof. Both a separate independent guarded-author artifact
audit and a separate independent review of this workflow and runbook are
required before any real launch. Capture actual exits, preserve failed runs,
and use stable HEAD through preparation.

The guarded-author artifact auditor counts all direct inputs, including the
five `Init` imports: its receipt records 16 edges rather than the 11 declared
project imports. `test_author_audit_gate.py` executes the runbook's actual
ancestry gate against that independent receipt, accepts 16, rejects 11, 15
and 17, and refuses optimized Python. Its observed outcomes and exact input
hashes are recorded separately in `author-audit-gate-observation.json`.

A future matched run would inherit the historical parent, external ancestry
and missing Foundation-wrapper outer exit boundaries. It would not alone
establish current-source provenance, formal PDF semantics, or identification
of the selected translated consistency sentence with untranslated Con(ZFC).

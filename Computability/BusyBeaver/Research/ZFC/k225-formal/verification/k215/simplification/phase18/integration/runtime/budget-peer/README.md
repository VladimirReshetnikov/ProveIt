# Forward-certificate resource review

The first phase18 build stopped at `KSource215FwdCheck12`, attempt 019. Its
preserved record reports a 120-second limit, timeout, exit −9 after 124.318
seconds, an empty compiler log and no accepted output object. It was not added to
`completed.json`. The terminal outer record is FAIL/exit 1. Twenty-three providers
remained accepted: eighteen fresh checks and five phase17 reuses.

`review.json` independently accepts the exact one-line resource successor and the
executed guarded owner migration. The new helper changes only newly invoked
`KSource215FwdCheck*` limits from 120 to 900 seconds. Sites retain 900 seconds;
ordinary modules and audits retain 120 seconds. Source, statements, exact
profiles, memory, workers and the shared compiler lock remain unchanged.

The review read all transition snapshots, both owners and the independently
derived preflight owner, all 1,084 inputs and eight absences, the unchanged
inventory, and all 23 retained source/object/log/record bindings. Only the runner
hash and its path/hash input changed. Original successful forward checks retain
their truthful 120-second records. Failed attempt 019 remains FAIL and must be
recompiled as attempt 020; it is never promoted.

This receipt covers the policy and metadata transition. The complete resumed
build still requires terminal PASS and the separate actual-result review. This
review invoked no compiler or supplied helper and changed no canonical files.

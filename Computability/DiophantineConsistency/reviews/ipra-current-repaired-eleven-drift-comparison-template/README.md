# Pending 172-module comparison

This independently reviewed comparator and subprocess-exit wrapper are
**unexecuted against successful replays**. They must be copied into separate
fresh verification directories after both 172-module Lean processes have
actually exited successfully. The wrapper records its child comparator's exit;
its own tool-session exit must be observed separately.

The comparator checks all 172 output/log and direct-input rows, full selected
overlays and inherited gates, both endpoint axiom reports, 1,104 workspace
paths, and all present and absent fallback companions. It reconstructs the
exact 3,440 new fallback candidate paths and requires the 2,140 inherited
records to equal the authenticated 107-parent manifest. Source-current status
is only a conjunction of the two runs' before/after drift scans and fresh final
comparison scans; it is not continuous monitoring. The inherited 848-project,
package-transitive and dynamic-import boundaries remain.

Six missing-plan/identical-run/shared-state negative probes passed and are
recorded in `comparator-negative-checks.json`; the prior receipt before the
fallback-map hardening is also preserved. An initial checker invocation failed
because the builder scripts had not yet been copied into this test directory;
`initial-missing-builder-failure.log` records that failure. None of these
probes is a successful replay or comparison.

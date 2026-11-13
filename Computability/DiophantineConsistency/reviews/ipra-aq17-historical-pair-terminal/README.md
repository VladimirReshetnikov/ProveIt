# AQ17 historical matched-pair terminal observation

The original launch session `86789` actually exited 0. Its full tool-provided
output is recorded in `outer-terminal-observation.json`; the coordinator
printed `author exit 0`, `peer exit 0`, and `MATCHED_SELECTIVE_PASS 44 affected
modules`. The separately captured coordinator observation has exit 0 and
binds the pair-state SHA-256
`6358d9259cee70182a619afb7422b059dd6d9d9dc3775de2229ab87d27397bb3`.
The exact launcher and both process logs are retained here.

Both original sibling states and all 88 module logs are copied here; each log
was rehashed against its sibling state during copying. Each state reports
44 successful additions and 109 named diagnostics. The earlier
[preparation packet](../ipra-aq17-historical-preparation/README.md) records the
observed freezer and preparer exits, equal HEAD gate, frozen snapshot and 15
historical-parent workspace drifts.

The subsequent [independent complete-result audit](../ipra-aq17-historical-pair-independent-audit/README.md)
passed. The complete original run remains
at `/tmp/ipra-aq17-historical-paired-run-01`. Results use the historical parent
and inherit package-transitive, dynamic and between-observation limitations;
the Foundation wrapper's outer exit was not captured, although its inner Lake
exit and the independent provider verifier's exit were observed as zero. The
mathematical identification of the selected consistency sentence and the
display-to-Lean connection are separate obligations.

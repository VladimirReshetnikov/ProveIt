INHERITED SOURCE-CONTEXT COLLECTOR

This is a selected portable subset of the context-collection portion of
pa196_research_2026-11-13.zip. UPSTREAM_SUMMARY.txt is the original report
and refers to other original files not selected here. Its new-result and
reproduction statements refer to that earlier archive, not this investigation.
The exact retained input pins and hashes are in inputs/source_manifest.json.

To regenerate the 2,219-context invariant, from this directory run:

  python3 source_contexts.py --output /tmp/pa_context_replay

Compare the generated source_contexts.txt byte-for-byte with the supplied
source_contexts.txt; compare receipt semantic fields, excluding timing.

To rerun the independent 353-fixture finite regression against the retained
contexts, run with assertions enabled:

  python3 validate_contexts.py

The latter writes validation_receipt.json in this directory. The collector
checks 4,959 symbolic branch cases and the exact 58,154-step startup. The
all-natural claim depends on the symbolic run/list arguments stated in the
original summary; this is not a proof-assistant kernel certificate.

The current third-row extension and positive controls are in the parent
local_search directory; its run_search.py is the portable current runner.

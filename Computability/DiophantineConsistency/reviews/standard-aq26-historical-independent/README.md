# Independent review of the historical AQ26 extension workflow

This packet reviews the paired-extension preparation and its **toy controls**;
it does not run the AQ26 proof or authenticate the still-running real parent.
The production task policy was compared with the independently recorded
successful author additions manifest: all 30 sources, their order and imports,
79 diagnostic names across 22 reporting modules, eight empty-report modules,
and the final target agree exactly. The builder and comparator independently
check each addition's exact diagnostics and allowed Lean metatheory axioms.

[`audit.py`](audit.py) copies the reviewed scripts into a disposable workspace,
reruns the five controls and their optimized-Python rejection checks, and adds
an independent control that forges the same forbidden `Classical.em` axiom in
both siblings' nonterminal reports and logs. The comparator must reject it.
The controls include actual Lean on toy modules, an observed toy freezer exit,
and a synthetic Foundation provider. The script pins and rechecks the tested
source hashes, and its [receipt](receipt.json) records actual results.

The first independent attempt used a temporary copy without the expected
repository directory depth and exited 1 before the freezer control could load
the planner. That was a reviewer fixture-layout error, not a production test
failure. The correctly nested independent run and additional mutation are
recorded separately. Neither successful toy controls nor this review prove
the real AQ26 endpoint, authenticate package-transitive or dynamic ancestry,
or guard against transient changes between observations.

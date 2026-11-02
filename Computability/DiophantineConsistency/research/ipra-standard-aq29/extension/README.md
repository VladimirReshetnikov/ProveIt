# Dedicated strict extension for standard-iPRA AQ29: toy-tested only

The production scripts in this directory fork the existing reviewed
[`reference-coherent-replay/extension`](../../reference-coherent-replay/extension/)
workflow into a separate task so the reference policy and its tools remain
unchanged. [`verify_fork.py`](verify_fork.py) pins the six original production
sources and checks byte identity after the permitted task substitutions: the
planner's two draft names and target, the preparer's policy path, and the
freezer's four exact declaration names. The builder, comparator and pair
coordinator are byte-identical to the pinned reference sources. These checks
do not independently verify the original workflow's correctness.

The [task policy](task-policy.json) binds `IPRAStandardAQ29Checks` to the
same-language presentation comparison and the three standard-AQ29 client
statements. A real run requires a completed and independently authenticated
matched parent pair, its separately observed terminal exit, a strict
current-source plan, a frozen and authenticated extension, separately copied
parent seeds, compiler-resolved imports, and two matching extension runs.
The running v2 parent snapshot is historical due to later source edits. This
freezer requires a strict `current` plan with zero parent drift and checks the
workspace against the parent snapshot: it therefore cannot run directly on
that v2 parent while those edits remain. A coherent, source-current successor
must pass first, or a separate historical-basis workflow must be reviewed.

[`control-receipt.json`](control-receipt.json) records seven controls including
the fork/policy bindings, source and selection rejection tests, a real-Lean
paired extension on a synthetic parent, and an end-to-end toy that invokes an
actual freezer and captures its exit. The [outer observation](control-observation.json)
records the control runner's exit 0. These use toy theorems and a synthetic
Foundation provider. They establish neither the standard-theory source nor
the endpoint theorem. Independent review of the dedicated adaptation is
pending. No real AQ29 extension has run; its upstream Foundation wrapper exit
was not recorded, and package-transitive, dynamic and transient-mutation
ancestry remains subject to the parent's documented limits.

# Checked translation into Foundation ZFC

The unchanged 457-line [Translation source](Lean/ZFCinPA/Translation.lean)
passes a fresh Lean check and **15 axiom probes with 17 typed clients**, with
zero warnings. The [actual record](results/translation-verification.json)
checks `zfc_proves_conZFCSet n`: for each external natural number `n`,
Foundation's ZFC proves the corresponding bounded-consistency sentence.
This is a numeralwise theorem; it does not yet supply the uniform internal
proof selector or the final PA-to-binary-machine equivalence.

The translation splits flat de Bruijn indices at the binder depth and
preserves evaluation for matching environments. In an arbitrary nonempty
Foundation ZFC model, it extracts all nine semantic ZFC clauses required
by the bounded-consistency development. Replacement first totalizes a
partial functional relation using the identity value when no output exists;
Separation then carves its image back to exactly the original relation's
image. The endpoint combines this model-relative extraction with the checked
bounded-refutation theorem and Foundation completeness. Model existence is
not assumed as a new theorem.

Source and audit took 11.527 and 2.762 seconds under one shared 120-second
deadline, one thread and 4,096 MiB. The source's existing `maxRecDepth 8000`
remains unchanged; the audit uses default proof limits and the source's
local opacity choices. All probes report only standard Lean axioms. All
293 recorded inputs and the newly captured first-provider object remained
unchanged after the audit.

The guard combines the actual [AxiomTruth](../../../SetTheory/BoundedConsistency/axiom_truth_check.md)
and [Foundation Z](foundation_set_theory_check.md) results: 30 selected
prerequisite modules, three explicit opaque cached boundaries and Init.
It preserves the six selected Foundation modules' companion artifacts and
the sparse namespace mirror. CounterModel, Cardinal.Basic and IsEmpty remain
cached boundaries; no whole-cache verification is claimed. Translation has
no `module` header and emits one fresh `.olean`; Foundation's four-artifact
requirements remain separately checked.

The [publication](results/translation-publication.json) and
[history](translation/history.json.gz) retain the original source-only plan,
actual-parent guard, exact snapshots and logs. The focused
[independent guard/audit review](translation/peer-review.json) and its
[history](translation/peer-history.json.gz) record the mixed parent schemas,
provider selection and proof limits. This check closes one entry in the
original validator dependency inventory.

# Preventive direct tactic import for the pair-evaluation bridge

This inert `.lean.src` snapshot is the reviewed `PairEvalRingBridge.lean`
with exactly one line prepended: `import Mathlib.Tactic.LinearCombination`.
The proof bodies, namespace, theorem statements and all original clients are
unchanged. Its purpose is to make that standalone module's use of
`linear_combination` explicit rather than relying on transitive tactic imports.

A source-level traversal did not find the tactic module through the bridge's
current imports, but unavailable source leaves prevent concluding it is
absent. No Lean failure has been observed. This is a preventive patch, not a
confirmed fix or proof that the import is necessary, available coherently or
sufficient. No Lean run, provider compatibility, root74 overlay refactor,
iPRA endpoint, physical-byte or PDF claim is made. Applying the snapshot later
requires a separate source/overlay update, fresh dependency inventory and
provider review; the existing reviewed chain and its receipts remain untouched.

Independent source review: [explicit tactic import](../../reviews/ordinary14-pair-eval-linear-combination-patch-independent/README.md).

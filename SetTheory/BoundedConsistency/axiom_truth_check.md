# Checked truth of the internal ZFC axiom codes

The unchanged [`AxiomTruth`](Lean/BoundedZFCConsistency/AxiomTruth.lean)
passes a [local Lean check](results/axiom-truth-verification.json). Its
`axiomCodesTrueAt` theorem discharges the remaining axiom-truth premise of
the [bounded calculus soundness result](level_soundness_check.md), under
the explicit `ZFCAxioms` semantic bundle. This adds power set, regularity
and choice to the six axioms used by the truth machinery.

The seven fixed axioms use quotation and satisfaction preservation. The
Separation and Replacement cases handle arbitrary internal formula codes,
including codes that need not quote an external formula. At a fixed
external level, the truth predicate is an object-language formula;
Separation and Replacement applied to that formula supply the required
sets. The renaming identities preserve all schema parameters.

The resulting `noBoundedRefutationAtLevel_zfc` excludes internally coded
refutations bounded at every formula occurrence by the external numeral.
Bundle extraction and classical completeness then give
`zfcprov_conZFCForm n`: a ZFC derivation of the bounded-consistency sentence
for each external natural number `n`. No axiom-truth or soundness premise
remains in this derivation family. Its type does not quantify `n` inside
the object theory. The source's discussion of unprovability of a uniform
sentence is explanatory, not a further formal theorem checked here.

All 29 axiom probes and 31 explicit typed callers pass with zero warnings
and only standard Lean axioms. Source and audit took 1.545 and 0.391 seconds
with one thread, 4,096 MiB and a shared 120-second deadline. The source's
existing `maxRecDepth 8000` is retained; the audit uses default proof limits
and the source's local opacity for `sealF`. The actual soundness check
supplies 23 project source/object pairs plus Init. All 176 recorded inputs
and the fresh object remained unchanged after the audit.

The [publication](results/axiom-truth-publication.json) and
[history](axiom-truth/history.json.gz) retain the exact source snapshot,
typed audit, dependency bindings, source review and raw logs. This checks
the bounded-consistency result in the repository's set-theory calculus.
Translation into Foundation's calculus, the remaining validator chain and
the final PA/240-state equivalence still require their own checks.

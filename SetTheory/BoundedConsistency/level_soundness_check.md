# Checked fixed-level truth and calculus soundness

The unchanged
[`LevelSoundness`](Lean/BoundedZFCConsistency/LevelSoundness.lean)
passes a [local Lean check](results/level-soundness-verification.json).
It proves renaming and substitution for arbitrary internal formula codes,
variable maps and universe environments, on both polarities at each fixed
external truth level. The successor-shift and variable-instantiation
interfaces preserve their codehood and environment hypotheses.

The proof constructs a set carrier from the environment graph, then reuses
the carrier-relative composition identities. Definable code inductions
handle potentially nonstandard codes; the recursion on truth levels is
external. The polarity-switch rank guards remain explicit.

The names `AxiomCodesTrueAt`, `LevelTwoValuedAt` and `LevelSoundnessAt`
are predicates in this module. Its no-refutation theorem requires both
axiom truth and calculus soundness as premises. Checking this module does
not discharge either premise or the final PA/240-state theorem.

All 21 named axiom probes and 21 explicit typed callers pass with zero
warnings and only standard Lean axioms. Source and audit took 1.068 and
0.340 seconds with default proof limits, one thread, 4,096 MiB and a shared
120-second deadline. The guard reuses 20 exact project source/object pairs
and Init from the actual [axiom-code](axiom_code_check.md) and
[universe-truth](universe_truth_check.md) checks. It retains the parents'
original source options and the Level parent's 46 audit warnings; those
modules were not replayed. All 134 recorded inputs remained unchanged.

The [publication](results/level-soundness-publication.json) and
[history](level-soundness/history.json.gz) retain the source snapshot,
audit, guard, dependency bindings and raw logs.
The independent [source/API/guard review](level-soundness/peer-review.json)
and [actual-result review](level-soundness/peer-actual-review.json) find no
blocker; their [history](level-soundness/peer-history.json.gz) is retained.

The unchanged
[`LevelCollapse`](Lean/BoundedZFCConsistency/LevelCollapse.lean)
also [passes](results/level-collapse-verification.json). For arbitrary
internal formula codes, truth and falsity certificates descend to a lower
external level under the corresponding oriented rank bound. The proof then
establishes exclusivity without a rank bound, totality for bounded codes,
and `levelTwoValuedAt H n`. The universal and existential polarity-switch
biconditionals retain their rank guards. These results discharge the
two-valuedness obligation, while calculus soundness and axiom truth belong
to later modules.

All 30 probes and 30 typed callers pass with zero warnings and standard
axioms. Source and audit took 1.796 and 0.378 seconds under the same default
limits. The actual substitution result supplies 21 project pairs plus Init;
all 145 recorded inputs remained unchanged. The
[publication](results/level-collapse-publication.json) and
[history](level-collapse/history.json.gz) preserve the complete check and
an audit-writer text-processing error corrected before any Lean invocation.

The unchanged
[`LevelSoundnessProof`](Lean/BoundedZFCConsistency/LevelSoundnessProof.lean)
now [passes](results/level-soundness-proof-verification.json) as well. It
discharges `LevelSoundnessAt H n` using the 17 bounded rule cases and
definable induction on the derivation's internal rank. Every formula-valued
rule parameter retains the required bound. The theorem transports truth
from the coded context to its conclusion; it requires no additional
soundness assumption. The final no-refutation corollary still requires
`AxiomCodesTrueAt H n`.

Its 14 probes and 14 explicit callers cover every public theorem and pass
with zero warnings and standard axioms. Source and audit took 1.234 and
0.288 seconds with default proof limits and the same resource limits.
The actual collapse result supplies 22 project pairs plus Init; all 156
recorded inputs remained unchanged. The
[publication](results/level-soundness-proof-publication.json) and
[history](level-soundness-proof/history.json.gz) preserve this check.

The subsequent [axiom-truth check](axiom_truth_check.md) now discharges
the last premise under the richer ZFC semantic bundle. The final
PA/240-state equivalence remains pending.

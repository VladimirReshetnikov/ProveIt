# Checked internal renaming and substitution

The unchanged [`InternalSoundness`](Lean/BoundedZFCConsistency/InternalSoundness.lean)
now has a fresh [local Lean check](results/internal-soundness-verification.json).
Despite its filename, this unit supplies the renaming and substitution layer;
coded-derivation soundness is a later module.

Renaming is total and unique on arbitrary internal formula codes, using
definable code induction. The satisfaction theorem identifies evaluation of
a renamed formula with evaluation under the composed environment. Its binder,
successor and instantiation identities retain explicit variable-map,
environment and set-structure hypotheses. Agreement with external quotation
is proved separately; no assumption that every internal code is a quotation
is made.

The check passes 15 named axiom probes and 15 typed callers, with zero warnings
and only standard Lean axioms. Source and audit took 3.434 and 0.288 seconds,
with default proof limits, one thread, 4,096 MiB and a shared 120-second
deadline. It reuses eleven exact project source/object pairs and Init from
the recorded bootstrap-frame check, with no external project dependency.
The selected pairs are validated; the other bootstrap prerequisites are
outside this check's scope.

The first source compilation passed, but its new audit opened the nonexistent
`LeanProofs.SetTheory` namespace. The corrected audit opens `SetTheory` and
`SetTheory.Form`; all statements and the proof source remain unchanged.
The [publication](results/internal-soundness-publication.json) and
[history](internal-soundness/history.json.gz) preserve both attempts, the
namespace correction, exact bindings, guards and raw logs. This check does
not establish existence of a set model or the final binary240 PA endpoint.

# Checked internal derivation soundness

The unchanged [`CodedDerivation`](Lean/BoundedZFCConsistency/CodedDerivation.lean)
now has a fresh [local Lean check](results/coded-derivation-verification.json).
It represents derivations by sets of judgements with ranks in the model's
internal omega. Every cited premise has strictly smaller rank. Definable
induction proves all seventeen inference rules sound at every internal rank,
including nonstandard ranks.

`derives_sound` retains explicit hypotheses for the internal set structure,
environment and satisfaction of the context. `not_derives_bot` rules out a
coded derivation of falsity from the empty context under the same structure
hypothesis. It does not construct that structure or prove consistency of ZFC.
External proofs are mapped to internal certificates in one direction; no
claim that every internal certificate is an external quotation is needed.

The check passes ten named axiom probes and ten typed callers, with zero
warnings and only standard Lean axioms. Source and audit took 4.301 and 0.277
seconds, using default proof limits, one thread, 4,096 MiB and a shared
120-second deadline. It reuses twelve exact project source/object pairs and
Init from the checked internal renaming/substitution result. No external
project dependency or dependency rebuild is involved.

The [publication](results/coded-derivation-publication.json) and
[history](coded-derivation/history.json.gz) retain the source review, guard,
audit, provider bindings and raw logs. The original, unexecuted audit draft
opened the wrong namespace; its corrected version was used for this first
successful run. Rank bounds, reflection and the final binary240 PA theorem
remain separate work.

# Contextual existential witness adapter

`contextExsElimWitness` adapts the previously checked existential elimination code to the branch context `insert q.shift (insert (∼p.free) Γ.shift)`, retaining the eigenvariable discipline. The existential and branch derivations are explicit hypotheses, and the output code agrees exactly with the existing graph for arbitrary valid model-valued inputs, including nonstandard ones. This is an internal model-level proof operation, not the full ordinal induction sequent or an iPRA result.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-exs-witness.sh "$REPO" FRESH_OUTPUT` to rebuild the source against the repository-replayed quantifier object and the prebuilt transitive overlays in the checker. It checks source and direct dependency hashes and rejects `sorryAx`; this is not a clean whole-workspace build.

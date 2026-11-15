# Order-isomorphism preserves zero

The Foundation natural-deduction proof `zeroFromIso` establishes in pure source first-order logic that `Ordinal.zero a` and `PairGraph.orderIso a b` imply `Ordinal.zero b`. It uses the typing and right-total clauses of the isomorphism graph; no ordinal-domain assumption or nonlogical source axiom is required. `zeroIsoStatementProof` gives the universally closed statement `∀ a b, zero(a) → orderIso(a,b) → zero(b)`, and `zeroIsoClosedProof` quotes its derivation into every internal source theory over a PRA model with IΣ₁ arithmetic reduct.

This is one fixed structural lemma for the proposed quotient-closed induction property. It does not yet derive the translated PA induction axiom, prove successor transport, or establish native iPRA/machine equivalence.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-order-iso-zero.sh "$PWD" /dev/shm/pa194-order-iso-zero-repo-NEW` from the repository root. The checker source-compiles the two modules in a fresh output, using pinned prebuilt dependencies including the source-replayed unified order-isomorphism syntax, and rejects `sorryAx`.

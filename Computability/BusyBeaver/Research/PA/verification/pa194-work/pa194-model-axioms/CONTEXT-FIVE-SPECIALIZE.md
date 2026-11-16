# Five-fold contextual specialization

`contextFiveProof` specializes five leading universal binders at arbitrary internally coded source terms under an arbitrary internal sequent context and theory. `contextFiveCode` gives the exact computed proof code, `contextFiveProof_val` certifies its value, and `contextFiveGraph_defined` gives one fixed Σ₁ graph. The model assumptions are PRA with an IΣ₁ arithmetic reduct. This is a proof-code operation; it does not itself supply the fixed greatest-image theorem or prove successor transport or native iPRA equivalence.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-context-five-specialize.sh "$PWD" /dev/shm/pa194-context-five-specialize-repo-NEW` at the repository root. The checker source-compiles this module against hash-pinned repository-replayed double and triple specialization dependencies. The successful output is `/dev/shm/pa194-context-five-specialize-replay`.

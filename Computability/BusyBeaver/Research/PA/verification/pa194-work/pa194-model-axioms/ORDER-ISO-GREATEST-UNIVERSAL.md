# Five-binder greatest-image sentence

The explicit arity-five typed formula `greatestImageBound` states that a given order-bijection sends a given greatest element to a given greatest element. `greatestImageOpen_fvSup` verifies that the original open formula has exactly five free-variable slots, and `greatestImage_closure` identifies its universal closure with `∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound`. The bound indices are 0 = graph, 1 = source, 2 = target, 3 = source point, and 4 = target point.

`greatestImageClosedCode_quote` proves that the previously computed internal closure code is exactly the quotation of this five-binder statement, in every PRA model with IΣ₁ arithmetic reduct. `greatestImageUniversalProof` supplies its proof in the full source theory. This does not yet supply a uniformly computed proof code or arbitrary model-index specialization, nor does it prove graph restriction or successor transport.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-order-iso-greatest-universal.sh "$PWD" /dev/shm/pa194-order-iso-greatest-universal-repo-NEW` from the repository root. The checker compiles both modules into a new output against hash-pinned prebuilt dependencies including the repository-replayed full-source greatest-image theorem. The successful output is `/dev/shm/pa194-order-iso-greatest-universal-replay`.

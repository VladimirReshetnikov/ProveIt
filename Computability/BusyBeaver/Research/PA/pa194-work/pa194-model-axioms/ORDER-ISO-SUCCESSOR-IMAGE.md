# The image of a successor's top point is a target predecessor

`successorHasGreatest` proves in Foundation natural deduction, using the explicit source equality principles, that if s is a successor of a then a is greatest in s. `successorImageWitness` proves that if g is an order-bijection from s to an ordinal b, then some edge of g carries a to a point y for which b is a successor of y. It combines the checked greatest-image existence theorem with the previously proved greatest-to-successor theorem.

Both are source natural-deduction constructions with explicit assumptions. The theorem does not establish that a and y are isomorphic; the graph restriction, successor cancellation, translated PA induction, native iPRA and machine equivalence remain open.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-order-iso-successor-image.sh "$PWD" /dev/shm/pa194-order-iso-successor-image-repo-NEW` from the repository root. The checker compiles the source in a fresh output against hash-pinned prebuilt dependencies including the repository-replayed greatest-image witness and greatest-to-successor theorem. The successful output is `/dev/shm/pa194-order-iso-successor-image-replay`.

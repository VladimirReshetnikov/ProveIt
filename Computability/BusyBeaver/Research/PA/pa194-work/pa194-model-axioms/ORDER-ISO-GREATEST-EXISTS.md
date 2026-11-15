# Existence of the greatest-image edge

`greatestImageExists` is a Foundation natural-deduction proof: assuming source equality principles and an order-bijection from a to b, each greatest element x of a has an edge to some y that is greatest in b. It obtains the edge from left-totality and uses the checked greatest-image theorem. The equality principles and the order-bijection are explicit premises. No uniform internal proof-code constructor or fixed source-theory axiom supplier is asserted.

This is a necessary ingredient toward successor transport. It does not construct a restricted isomorphism or establish successor transport, PA induction, native iPRA formalization, or the machine equivalence.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-order-iso-greatest-exists.sh "$PWD" /dev/shm/pa194-order-iso-greatest-exists-repo-NEW` from the repository root. The checker compiles this module in a fresh output against hash-pinned prebuilt dependencies including the repository-replayed greatest-image theorem. The successful output is `/dev/shm/pa194-order-iso-greatest-exists-replay`.

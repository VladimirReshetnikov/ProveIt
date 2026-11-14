Restricted allocation screen

Requires Python3 and z3-solver. From the packet root:

python3 search/allocation/allocate_symmetric.py source_reductions/essential158.json /tmp/essential-core --protected search/allocation/protected-core.txt --feasible-only
python3 search/allocation/allocate_symmetric.py source_reductions/essential158.json /tmp/essential-startup --protected search/allocation/protected-startup.txt --feasible-only

The first reports UNSAT in the modeled allocation family; the second reports EMPTY_DOMAIN. The model fixes old compatible readers, reserves rows required by existing helpers and the indicated protected-row set, maps new nodes injectively, and adds label-order constraints. This is not a general lower bound or a proof that no195-state machine can implement the program. A SAT result would still require fresh instruction and startup correctness proofs.

The original research receipts retain source paths used during the experiment; identify inputs by their SHA256 fields. The script is adapted from the pinned ProveIt allocator and includes exploratory label-order constraints. Upstream licenses and notices are retained in the packet.

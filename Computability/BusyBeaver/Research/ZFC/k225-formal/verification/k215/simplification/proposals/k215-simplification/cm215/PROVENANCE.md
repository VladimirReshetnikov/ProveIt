# Source provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: b6c7087477e51c017003bd729e712c8969733223

The exact native tables in `upstream/` are copied from:

- `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm`
- `Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/conditional-marker/machine/marker215.native.tm`

The first 808-line source under `BusyBeaver/Core.lean` is an unchanged copy of
`Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` at that revision. It is
included solely to reproduce the new adapter without a full repository build.
The original notices are retained in `upstream/`. The predecessor K215 proof,
CM215 construction, numerical calculus, compiler, and ordinary marker proof
remain contributions of their original authors; no new machine is claimed.

The new files in this packet are `PositiveStuttering.lean`, `CM215Data.lean`
(generated from the two pinned tables), `CM215Transfer.lean`,
`CM215CoreBridge.lean`, `CM215RepoBridge.lean`, the generator, and these notes.
They implement the small relative formal proof described in `proof_notes.md`.
The repository's `final_helper_reuse_search.py` was inspected as prior-search
context and is not included in this proof packet or needed for reproduction.

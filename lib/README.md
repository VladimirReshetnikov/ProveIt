# Vendored libraries

This is the repository's only home for vendored code.

[`Coq-BB5/`](Coq-BB5/) contains the selected BB2, BB3, and BB4 Rocq
certificates from `ccz181078/Coq-BB5` commit
`9142e219229baf2245d3f70851947230ea28a318`. Each subtree retains its upstream
license, provenance README, and repository-local kernel-hardening changes.

[`Coq-Synthetic-Computability/`](Coq-Synthetic-Computability/) is the pinned
MIT-licensed `uds-psl/coq-synthetic-computability` submodule at commit
`8fc0014f1b35f832e78d98f72dfef525aa39861f`. The repository-authored Turing-
degree wrappers and the tracked Rocq 9.2/stdpp 1.13 compatibility patch live
under [`../Computability/TuringDegrees/`](../Computability/TuringDegrees/),
not inside the submodule.

[`FormalizedFormalLogic-Foundation/`](FormalizedFormalLogic-Foundation/) is the
read-only Apache-2.0-licensed `FormalizedFormalLogic/Foundation` submodule at
commit `32e1a0956a8622fad067328ca1959729a7634428`.  It is retained as the source
reference for the independent Coq port under [`../Logic/Modal/`](../Logic/Modal/);
the port neither imports nor modifies the Lean checkout.

[`openai-math/`](openai-math/) is a ported 137-module subset of the Apache-2.0
Lean library of `openai/math` (commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
family 159): Ruzsa modelling, a Croot–Sisask/Sanders-type Bogolyubov lemma and
a hypergraph-removal Szemerédi theorem and their import closures, built as
the root Lake library `OAI`. It supplies Freiman's theorem, the
Balog–Szemerédi theorem and Szemerédi's theorem (Gowers catalogue
Theorems 7.1, 7.2 and 1.2) to
[`../Combinatorics/Ramsey/Lean/GowersSzemeredi/`](../Combinatorics/Ramsey/Lean/GowersSzemeredi/).
Its README records provenance, the backport modules under `OAI/Compat/`, and
every per-file port change. Its [`preprints/`](openai-math/preprints/PROVENANCE.md)
subdirectory holds an unmodified copy of the upstream manuscript directory
*The Exponential Time Hypothesis is False* (commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, Apache-2.0). It is the primary
source of [`../Computability/SubexponentialSAT/`](../Computability/SubexponentialSAT/README.md).

Repository-authored Busy Beaver models, bridges, and score certificates live
under [`../Computability/BusyBeaver/`](../Computability/BusyBeaver/), not here.

[`jeff-busy-beaver-zfc254/`](jeff-busy-beaver-zfc254/README.proveit.md) contains
the unchanged 254-state machine designed by Mira-Cult and Jeff's published
Coq verification, pinned to `jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`, with its exact build dependency
closure, attribution and source manifest. No upstream-wide license is
declared; this snapshot is excluded from ProveIt's blanket MIT-0 grant, and
its nested dependencies retain their own licenses.

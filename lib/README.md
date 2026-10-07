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

[`openai-math/`](openai-math/) is a ported 98-module subset of the Apache-2.0
Lean library of `openai/math` (commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
family 159): Ruzsa modelling, a Croot–Sisask/Sanders-type Bogolyubov lemma and
their import closure, built as the root Lake library `OAI`. It supplies
Freiman's theorem and the Balog–Szemerédi theorem (Gowers catalogue
Theorems 7.1 and 7.2) to
[`../Combinatorics/Ramsey/Lean/GowersSzemeredi/`](../Combinatorics/Ramsey/Lean/GowersSzemeredi/).
Its README records provenance, the backport modules under `OAI/Compat/`, and
every per-file port change.

Repository-authored Busy Beaver models, bridges, and score certificates live
under [`../Computability/BusyBeaver/`](../Computability/BusyBeaver/), not here.

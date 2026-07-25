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

Repository-authored Busy Beaver models, bridges, and score certificates live
under [`../Computability/BusyBeaver/`](../Computability/BusyBeaver/), not here.

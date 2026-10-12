# Code in this research delivery

`forest_search/` is a standalone finite graph/matrix solver and independent
certificate checker. It includes the polynomial two-row-column method,
complete stopping-witness search with deterministic caps, finite oracle
comparisons, mutation tests, and controlled benchmarks. The problem contract
and exact negative scope are documented in its README.

`replay_native_packets.py` replays the ten archived source packets against
an independently supplied, patched ProveIt checkout. It checks seven complete
positive cut censuses and three source-authenticated obstructions for the
fixed raw boundary kernel. It requires no Regina installation.

The proposed production modules are under `../native/` at their intended
repository paths. `../integration.patch` installs those modules, the two
entrypoint changes, and the native research/test files. The polynomial
forest-choice solver is not part of that native dispatch: its complete
source graph/matrix adapter remains a research interface with explicit
source authentication obligations.

All commands and dependencies are listed in `../REPRODUCE.md`. Recorded
observations are under `../results/forest_search/`, `../results/native/`,
and `../results/package_validation/`.

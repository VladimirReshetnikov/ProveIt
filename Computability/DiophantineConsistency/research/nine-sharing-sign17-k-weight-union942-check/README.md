# K Fin942 weight-certificate replay and union

This checked 40-stage attempt replays the independently audited Fin224
union, all six remaining audited pairs of weight batches, and six staged
`Fin.append` clients in one provider context. It proves a single Fin942
theorem for the candidate index/weight vectors. The runner pins the earlier
Fin224 and all six pair terminal receipts and compares source hashes before
replay. Recompilation in one context avoids assuming independently replayed
objects with differing hashes can be mixed. Candidate positions are not yet
proved actual physical ranks; ordering, control terms, full K and external
file/gzip binding remain separate.

Each child retains the existing 120-second, 4-GiB sampled-RSS and 10-GiB
available-memory limits, but the full sequential replay can occupy the Lean
slot for several minutes. Author no-Lean preflight exited 0 for 40 stages.
Runner SHA-256:
`92a146a0e3a0885fd06a9a98531ab33753eb727e72e873640dc929dfd01dcda6`;
manifest SHA-256:
`43b326e71f54283140b56a92717c6e47386326114cd0787ad9bc84e6c32a9a88`;
six-union source generator SHA-256:
`036ea7a2bf86c510e5aa7d1e67d3a4218219378fafba408a832ba1be6a84a287`.
Each generated source has its own manifest hash. The run used the established
independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-union942-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-union942-terminal-independent/README.md) passed; the packet is frozen.

# Materially distinct 215-state alternatives

Each directory is a complete 215-working-state blank-start machine that differs from the primary
[K215](../README.md) in design, not only by a state renaming or a source re-association. Their
ordinary proofs, as delivered, give `ZFC proves: not Halt(M, blank) <-> Con(ZFC)` from the
inherited numerical-calculus calibration. None has a compiled Lean or Rocq endpoint; the primary
K215's proof sources are described in `k225-formal/README.md`.

| Directory | Design | Placed |
|---|---|---|
| [commands120](commands120/README.md) | command order DROP/NIP/MP | batch 198 |
| [composed](composed/README.md) | composed command selector | batch 199 |
| [reencoded](reencoded/INTAKE.md) | re-encoded addresses, counter-1 seed | batch 200 |
| [zero-spare](zero-spare/INTAKE.md) | zero-valued spares, two-truth startup | batch 200 |
| [zero-spare-z201](zero-spare-z201/INTAKE.md) | NIP/MP/DROP order with zero spares | batch 200 |
| [zero-spare-transfer](zero-spare-transfer/INTAKE.md) | transfer-pop with append-zero spares | batch 200 |
| [mp-first-transfer](mp-first-transfer/INTAKE.md) | transfer enumeration with MP first | batch 200 |

Batch 200 kept only materially distinct implementations. Deliveries whose machines were state
renamings or re-associations of tables already here, and research-only packets, were retired
without placement; the batch-200 entry in `docs/incoming/README.md` lists them with their arrival
commits.

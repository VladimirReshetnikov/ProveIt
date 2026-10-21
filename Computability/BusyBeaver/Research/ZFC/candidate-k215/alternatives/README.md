# Materially distinct 215-state alternatives

Each entry is a complete 215-working-state blank-start machine that differs from the primary
[K215](../README.md) in design, not only by a state renaming or a source re-association. Their
ordinary proofs, as delivered, give `ZFC proves: not Halt(M, blank) <-> Con(ZFC)` from the
inherited numerical-calculus calibration. None has a compiled Lean or Rocq endpoint; the primary
K215's proof sources are described in `k225-formal/README.md`. The last two rows are not
directories here: they are Sources 165 and 166 of the
[zfc-closure-kernels](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/)
report, placed in batch 200, whose write is still to come.

| Directory | Design | Placed |
|---|---|---|
| [commands120](commands120/README.md) | command order DROP/NIP/MP | batch 198 |
| [composed](composed/README.md) | composed command selector | batch 199 |
| [reencoded](reencoded/INTAKE.md) | re-encoded addresses, counter-1 seed | batch 201 |
| [zero-spare](zero-spare/INTAKE.md) | zero-valued spares, two-truth startup | batch 201 |
| [zero-spare-z201](zero-spare-z201/INTAKE.md) | NIP/MP/DROP order with zero spares | batch 201 |
| [zero-spare-transfer](zero-spare-transfer/INTAKE.md) | transfer-pop with append-zero spares | batch 201 |
| [mp-first-transfer](mp-first-transfer/INTAKE.md) | transfer enumeration with MP first | batch 201 |
| [transfer215](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/166-transfer-mach-README.md) (Source 166) | transfer-pop command, 201-node source, partial-AX startup | batch 200 |
| [cb1_215](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/165-frontier-machine-search-README.md) (Source 165) | CB1 appended to the restoration loop; changed enumeration, calibrated by a separate scheduler proof | batch 200 |

Source 165's `normalized215` is a local stuttering normalization of `cb1_215` with the same blank
behavior, so it is not listed separately. `zero-spare-transfer` and `mp-first-transfer` both
descend from `transfer215`.

Batch 201 kept only materially distinct implementations. Deliveries whose machines were state
renamings or re-associations of tables already here, and research-only packets, were retired
without placement; the batch-201 entry in `docs/incoming/README.md` lists them with their arrival
commits.

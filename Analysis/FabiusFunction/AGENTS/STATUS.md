# Coordination switch for `Analysis/FabiusFunction`

This file is the single authority on whether the multi-agent coordination
framework is in effect.  Editing it (plus creating or deleting the board
branch it names) is the **entire** enable/disable procedure; no other file
anywhere changes state.  The protocol it switches is
[`PROTOCOL.md`](PROTOCOL.md).  Only the user directs a flip.

```text
state: OFF
protocol: v2 (PROTOCOL.md)
campaign: none
coordinator: none
board-branch: none
document-owners: none
since: 2026-08-26
```

While `state: OFF`, agents work in this directory one at a time and no
coordination rule binds anyone.  The engineering policy in
[`../AGENTS.md`](../AGENTS.md) (documentation, Lean builds, invariants)
applies at all times regardless of this switch.

## Campaign history

One row per campaign, newest first; keep at most five rows.

| Campaign | Dates | Retrospective (one line) |
| --- | --- | --- |
| v1 — registry/board on `main` | 2026-08-24 – 2026-08-26 | Quality held (serialized builds, dual review, no invariant regressions) but overhead was severe: ~18k lines of bookkeeping, grant queues, audited work stranded behind leases; replaced by v2.  Archive: git history — the deleted `docs/COLLABORATION.md` and `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, and `git log -- Analysis/FabiusFunction/docs/registry/`. |

# Sources and preservation boundary

The only mathematical input files read for this continuation are the supplied
proof and its independent audit, treated as inert text:

1. `/workspace/shared/arity-table-asymptotics-20261004/PROOF.md`
   SHA-256 `638e524d058deb926919d15b7df2dafc17f7a44dc2688b33e06ee24f476b7c41`
2. `/workspace/shared/independent-arity-asymptotics-audit-20261004/AUDIT.md`
   SHA-256 `7405fc28ea33b90ca80471ab368b667e1728b374eb3098f3e62844a91e1f8ca7`

Their manifest identities are respectively:

- `6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1`
- `737af333985bc079ecdd688f1854f7221bb86169db7841d91a1115d2f94e7055`

This packet derives its new inequalities directly from the exact sector
formula. It neither imports nor executes the supplied programs, scientific
code, source interpreters, physical/trajectory simulators, schedules or Lean.
All executable files in this packet were freshly authored and read in full
before execution. The exact checks use only Python standard-library integer
and rational arithmetic.

The explicit preservation boundary contains 51 filesystem objects: both input
directories and all their descendants, their two adjacent ZIPs and their two
adjacent receipts. `evidence/input-before.json` was captured at
2026-10-04T16:00:27.639334+00:00, after the initial inert reads and before the
new sector checker ran. `evidence/input-after.json` records an identical final
inventory: object paths and kinds, hashes, sizes, permission modes and
nanosecond modification times. Access times are intentionally excluded.
Neither source metadata nor source content was changed or restored.

The article being packaged in a separate task was not edited or included in
this continuation's boundary. No claim about unrelated active report trees or
their historical changes is inferred from the 51-object preservation result.

The source proof and audit attribute the sequence to OEIS A196460 and discuss
prior published interpretations and the known leading asymptotic. Those
attributions remain unchanged. This continuation did not redo their literature
search or independently retrieve the public references, and makes no priority
or novelty claim.

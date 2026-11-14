# Verification evidence

`construction_replay.log`, `commands_replay.json`,
`package_physical_replay.log`, `novelty_replay.json`, and `census_replay.log`
record successful runs of the portable programs delivered in this package.
The detailed independent contracts, generic-list lemmas, exact blank seed,
and receipt are under `independent/`.

The frozen independent checker includes a historical novelty check against
its original census. Its receipt field `same_size_prior_byte_forms` describes
that old census only. The authoritative current comparison is the separate
`novelty_replay.json`: five prior 194-state byte forms, three graph classes,
including the rejected scanner candidate. The new graph and its global
left/right reflection match none of those classes. `RESULTS.json` labels
the historical count explicitly and keeps the current certificate separate.

Symbolic step counters measure checker work, not physical runtime for
unbounded register values. The exact 57,922-step startup is a literal
blank-tape computation. No finite nonhalting prefix is used to establish
the consistency equivalence.

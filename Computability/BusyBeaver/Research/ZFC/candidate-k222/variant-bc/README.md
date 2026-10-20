# The second 222: Source 128 stacked with Source 129

A different 222-state machine, built at the batch 181 intake from:

- Source 129's seed-root 223 (C), 49 + 186 − 12;
- Source 128's merged equality row G (B).

It is 49 + **185** − 12: one node fewer than the [A + B 222](../README.md), and one sharing fewer.

## Construction

C rebuilds the whole bundle region (path `11101001001110`) from 164 closed units and an explicit
binary pattern. Its bundle word is `¬(RV → (H → ¬K_s))`: membership vacuity, then the helper,
then the seed core. B's idea, dropping the helper, becomes:

- delete H's 26 units (word positions 9–19) and one of the two final implication units;
- the word then emits `¬(RV → ¬K_s)`, checked with the 224 package's pinned executor.

Then come B's G row at the old ρ7 (global leaves 648–732) and B's closed rotation at
`1110100100111000`, which keeps the zero run at 6 ([code/bc_build.py](code/bc_build.py)). The
source has 4,744 leaves and **185 interior nodes**. It was compiled against C's K-labelled
table with the same incremental compiler as the A + B 222 (3 fresh states, 26 reused), and B's
two source-dependent folds then applied to the same nodes: 222 states.

Its calibration composes Source 129's seed-K argument with Source 128's G equivalence. The
equivalence treats the K core as opaque, so it applies to the seed core. The seed
presentation is already calibrated in Elliot Glazer's Rocq development
(`KPSeed.output_root_to_seed`, `KPrimeCore.seeded_core_to_kp0`). So this 222 is the better
proof-assistant target: unlike the A + B 222, it needs no conditional-K hereditary-domain
interpretation.

## Verification

| Check | Result |
| --- | --- |
| Unbounded runtime ([receipt](evidence/runtime222bc.json), [cases](evidence/runtime222bc_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,167** cases, **1,488,390** symbolic rules, all 444 rows, minimum duration 13 |
| Exact blank startup ([record](evidence/boot.txt)) | 409,835 steps |
| Finite screen ([record](evidence/screen.txt)) | 0 failures |
| Emitter ([record](evidence/emitter_check.txt), [code/verify_emitter2.py](code/verify_emitter2.py)) | helper gone from the bundle, nothing else changed; row = G; leaves = C's with exactly two word substitutions |
| Exact bisimulation minimization ([code/minimize.py](code/minimize.py)) | already minimal |

Canonical SHA-256 `3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476`; inherited
`14cbb21d4216e95fd4498c46f2a63869437c59065b537ebe17b8183cf29d0769`; source
`cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e`.

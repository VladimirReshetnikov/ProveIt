# Batch 214 placement: Sources 188–192

These five manuscripts arrived, in the order below, in
`c3caaf63a4e1b391426501b6bda21f4992d4465f`. Merge
`fe1f40e533585efd950db39e466343fc0f3bdb9c` retains all five ZIPs exactly.
All five name reviewed commit `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
They continue this report's K215 logical-interface and proof-simplification
work, so they are additions with the next local source numbers, 188–192.
The collection count remains 290. Written reconciliation and catalogue changes
follow placement separately; placement itself assigns no new formal status.

## Recovery and payload

The [complete map](data/intake214-placement.json) accounts for **1,161 members,
16,988,562 expanded bytes**. It uses 799 immutable Git aliases, 44 earlier
delivery-member aliases, 67 arrival-only members, and 251 new ancillary files
(3,176,007 bytes). The new files comprise 106 code/build/proof files, 123 data
records, and 22 prose files. Proposed Windows paths, including `C:\ProveIt\`,
are at most 157 characters.

Of the Git aliases, 797 bind the exact tree of `fe1f40e533585efd950db39e466343fc0f3bdb9c`;
two report READMEs bind the reviewed `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`
tree. Each alias was compared with its complete delivered bytes. The remaining
unique bodies have no matching blob in the reachable Git-object history;
there is no unresolved historical match in this census. This is exact byte
deduplication, not a claim that different source files have different results.

Source 188's embedded phase12 evidence archive is itself an exact immutable
Git alias. Its 167 regular members were inventoried as inert data; the archive
is not copied again or executed. Its inner members are not added to the
1,161 outer-member total.

| Manuscript / Source | Arrival ZIP | Members | Git / delivery / arrival / new | New bytes |
|---|---|---:|---:|---:|
| 01 / 188 | `Further_Proof_Interface_Simplification_2026-10-22.zip` | 335 | 295 / 0 / 4 / 36 | 1,227,305 |
| 02 / 189 | `K215_Direct_Seed_and_Shared_Normalization_2026-10-22.zip` | 5 | 0 / 0 / 3 / 2 | 1,265 |
| 03 / 190 | `K215_Proof_Simplification (1).zip` | 269 | 106 / 14 / 27 / 122 | 956,645 |
| 04 / 191 | `K215_Proof_Simplification.zip` | 341 | 261 / 15 / 20 / 45 | 598,194 |
| 05 / 192 | `K215_Proof_Simplification_2026-10-21 (2).zip` | 211 | 137 / 15 / 13 / 46 | 392,598 |

The 67 arrival-only members are 17 main READMEs, manuscripts, PDFs and article
inputs, plus 50 unique log bodies excluded by existing ignore rules. The
article inputs include Source 190's `article/measurements.tex` and Source 191's
`verified-metrics.tex`; their figures are part of the delivered manuscripts.
Exact duplicates may point to those original members through delivery aliases.
No main manuscript, main README or PDF is newly placed in this host.
Checksum-manifest contents were not inspected or validated. Such files follow
the ordinary prefix and existing ignore rules. No line-ending investigation,
normalization or attribute exception was made.

Placed copies follow existing Git attributes. If a placed file differs from its
delivered bytes, the helper requires equal Git clean hashes under that exact
repository path, then recovers the original raw bytes from the committed ZIP.
It records every such attribute-equivalent path. Content changes with unequal
clean hashes are rejected; no payload or attribute rule is altered.

All new ancillary names use the source prefix and a short topic slug. Where
basenames would collide, the path includes a short parent hint; the map retains
every complete original member name and its destination. Delivered relative
paths inside source files and records are unchanged. Recover the original
layout before using those paths; placement does not make their bundled build
commands maintained production commands.

## Reasons for the five additions

**Source 188** develops a common `QHyp` interface for the CP/GIC semantic
argument, conditional opaque-prefix Home templates, and small dispatch/import
refactors. The retained [QHyp proposal](code/188-interface-CPGICQHyp.lean) and
[Home proposal](code/188-interface-OpaquePrefixHome.lean.proposal) are research
inputs. In particular, the all-prefix Home lemma and its conversion into the
current complete site contract remain obligations; a finite template census
is not a kernel theorem or a reduction of the machine's 6,176 branch obligations.

**Source 189** is a short mathematical continuation of the direct-seed route:
use a narrow seed schema with the original named semantics and combine the
freshness inequalities. The [source audit](data/189-seed-SOURCE_AUDIT.json) is
retained. The packet ships no checked implementation; the direct seed does not
license identifying literal named equality with its translated semantic image.

**Source 190** combines an alternative shared implication basis with an
exact-port residual site interface. Its [residual source](code/190-residual-BusyBeaver-ZFC-KResidual215.lean)
separates decoder prefixes from positive residual execution. Submitted component
records and failed drafts are retained, including the explicitly unchecked
endpoint patch. The residual interface remains a distinct prospective proof
route. Its older shared-basis construction overlaps the already checked phase13
work; its component claims do not establish a new exact K215 endpoint here.

**Source 191** carries the phase13 shared-basis result again, a narrow
[direct-seed implementation](code/191-direct-KSeedDirect222.lean), and Rocq
boundary-sharing experiments. Its generic endpoint/component claims do not
mean that the exact `KEndpoint215` closure was checked by this intake. The
shared-basis source pair is already represented by exact Git aliases.

**Source 192** combines that shared basis with a dense-bridge proof refactor
and extraction of a small [PowerSets interface](code/192-powerset-PowerSets.lean).
The distinction between selected import-closure savings and total source size
is retained. Submitted Lean component checks and Rocq 8.18 experiments remain
delivered evidence; they are not new compiler executions or a change to the
maintained Rocq 9.1 boundary.

The five main reports and READMEs were read before these placement choices.
The ordinary reviews found no prerequisite retraction of the currently checked
construction. No supplied verifier, generator, proof compiler or archived
executable was run. The current machine and maintained proof sources are not
edited by this placement.

## Recovery check

The own [recovery helper](code/intake214-recover.py) reads immutable Git blobs
and the placed raw ancillary bytes. From the repository root:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake214-recover.py --verify-only
```

Use `--out /absolute/new/scratch-directory` instead to reconstruct all five
original directory layouts. The output directory must not exist. This reads
archive members as data; it does not invoke a delivery's code.

The [pre-placement receipt](data/intake214-recovery-plan.json) verifies all
1,161 members using the external extraction for the 251 proposed new files.
It explicitly makes no claim that those files were already placed. The original
strict raw-byte helper and its receipts are preserved in the scratch handoff
history; the successor follows the repository's existing text-attribute policy. The
[negative controls](data/intake214-recovery-controls.json) reject a changed
archive identity, changed Git-alias digest, invalid delivery alias, missing
member and a content mutation. A separate positive control checks the actual
staged `Codes230.v` bytes using the existing Git clean filter. Their [own source](code/intake214-controls.py) records the historical
scratch-only planning invocation. The placement owner performs the same helper
without that planning override after copying the payload. The five ZIPs can
then be retired in the placement commit while remaining recoverable from the
immutable arrival above.

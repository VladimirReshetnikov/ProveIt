# Source and formalism experiment ledger

The selected construction is GC215. The other sources are research probes with the statuses below; they are not additional accepted Turing-machine candidates.

Repository baseline: `34b63b3b197b0a5f285a229d91bc163fcc42ab93`. Date: 21 October 2026.

A source DAG count includes every distinct binary source subtree, including leaves. It is not a Turing-machine state count. “Leaves” means primitive occurrences in the unshared syntax tree.

## Exact source representatives

| Construction | DAG | Leaves | Status |
|---|---:|---:|---|
| Use tag register C as GEN binder | 202 | 4,732 | selected 215 state candidate |
| Move the transfer halt test to incoming T; fuse test with clearing T | 203 | 4,720 | source priced no 215 allocation |
| Top guard with the existing H-copy loop followed by H-clear | 203 | 4,726 | source priced no 215 allocation |
| Consume H while checking H=1, then pop W into H | 205 | 4,722 | source priced no 215 allocation |
| Remove the transfer halt test | 198 | 4,716 | invalid as standalone candidate |
| Guard incoming T=1 at AX entry, with guardless transfer | 205 | 4,722 | abstractly calibrated source priced |
| Fuse GEN temporary-stack traffic into direct register copies and pairing | 206 | 4,702 | source priced no 215 allocation |
| Consume H during GEN and let later B field start at zero | 205 | 4,728 | source price only |
| Reverse Cantor arguments in all formula constructors while retaining stack coding | 208 | 4,732 | source priced abstract codec argument |
| Emit rho6(U,A) early, with U<=A, while reusing the consumed cache register | 217 | 4,731 | logical restriction proved source price only |
| Combine direct transfer with known joint rho2/rho4 parameter permutation | 201 | 4,732 | source priced no new candidate |
| Use NIP;DROP;NIP as the sole stack primitive | 201 | 4,775 | prior comparator uncalibrated |
| Use the incoming theorem as GEN binder by deleting the first parameter push | 203 | 4,725 | uncalibrated source probe |

The JSON companion gives each representative’s archive path, SHA-256, depth, maximum zero run, input hash, and precise scope. Every representative and both additional companion variants are included. The selected source is shared with `source/gc215.sites.json`; the other outputs are under `research/sources/`.

## Reproduce the cost claims

From the archive root:

```sh
python3 research/sources/audit_costs.py
```

This checks every delivered source hash and recomputes its distinct-subtree count, primitive count, maximum depth, and maximum zero run. It also verifies the hashes of the archived receipts. It does not prove source semantics, reproduce optimization runs, or validate a binary machine. The main candidate’s separate universal runtime and startup checks are documented in the main README.

## Scope of the alternatives

The 23-leaf incoming-top transfer has 203 DAG nodes. The tested narrow allocation lacked two roles; an optional MILP run timed out without an incumbent. Neither fact is a global state lower bound. The copy-and-clear variant also has 203 nodes.

The fused incoming-cache test preserves the original transfer contract and uses 25 leaves. Twelve tested equivalent layouts had 205 DAG nodes, and a subsequent bounded beam found no improvement. The guardless 198-node source has no halt instruction and is invalid as a standalone candidate. Relocating the guard to AX is logically calibrated, but its best recorded layout has 205 nodes.

Directly fusing GEN’s temporary stack traffic reduces its prefix from 81 to 51 leaves. Across four scratch schedules, four increment orders, and five Catalan associations, the best of 80 recipes has 206 DAG nodes. The separate destructive-cache probe saves four leaves but has 205 nodes; its altered whole-command interface was not calibrated.

Mirroring Cantor arguments in the four formula constructors while preserving stack coding has a recorded cost of 208 nodes. The formalism-side code calibration is separate from physical implementation; no competitive table or universal binary runtime was obtained for this source.

The restricted-sixth-row source emits the instance with binder U and matrix U+x before consuming U. Its 4,731-leaf representative has 217 DAG nodes and a maximum zero run of eight. It is a source prototype requiring a different layout or scanner before it can become a competitive machine. The companion that swaps the physical orientation of all later rows has 224 nodes.

The joint row-permutation sources retain 201 nodes, but the tested allocation did not yield a new accepted machine. The permutations themselves already appear in the incoming corpus. The modified GEN_C census is a separate experiment on the new binder interface.

The rotating-pop source has 201 nodes and a 215-state table, but that table is byte-identical to an incoming comparator. Its primitive runtime and startup were checked, while its intended strong compiler remained obstructed. It is neither new nor calibrated. The theorem-binder probe also remains uncalibrated and has 203 nodes.

## Recorded search bounds

| Seed | Trials | Distinct roots | Best DAG |
|---|---:|---:|---:|
| beam215 | 168,943 | 164,699 | 202 |
| beamST215 | 183,884 | 179,360 | 201 |
| beam_genC | 181,374 | 178,720 | 202 |
| beam_fused25 | 179,641 | 177,004 | 205 |

These finite-width, seeded searches establish only their recorded outcomes. The separate GEN_C row census exhausts the 279,936 recipes in its fixed 6^7 family and has four minima, all with 202 nodes. It does not exhaust source re-associations or other encodings.

## Evidence and provenance

Archived optimizer and experimental receipts are preserved verbatim under `research/sources/receipts/`. Their hashes are recorded in the JSON ledger. Internal paths in those historical receipts identify the original research workspace; they are not promised archive-relative paths. Fields named `historical_id`, `historical_directory_id`, and `historical_generator_id` have the same meaning. The corresponding source outputs are included even where the historical optimization generator is omitted.

The first GEN_C216 allocation failed because it overwrote engine row 134/0 despite passing prefix checks. That rejected table is not used. The corrected parent, SHA-256 `f0b7ae5e41fb6445afd1bf5e1618f6dd059c1dacbce47d3f81086ef69da33629`, passed all 6,151 primitive cases and all 432 rows. Only that corrected parent underlies GC215. Its historical runtime receipt is included; the final GC215 runtime is separately replayed by `verify.py --runtime`.

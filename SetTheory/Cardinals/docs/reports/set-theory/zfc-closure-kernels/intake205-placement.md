# Batch 205 supplemental placement references: Sources 168–173

This is supplementary reconciliation of the **existing batch 205**, whose six archives arrived in `a6b3a3001110bee41c906452b5f36cb5b8501968` and were placed and retired by `35ba151c3bd6289161e0c1eee864ac4328e611a0`. It does not create another batch, repeat the payload placement, retire any ZIP, or change the queue/catalogue. Sources 168–173 follow archive order A–F. Sources 165–167 and their historical records are untouched.

The [complete recovery/reference map](data/intake205-placement.json) retains every original path, byte count, SHA256 and Git blob ID for all **851 members / 29,276,389 bytes**. Its immutable Git references identify the exact commit and path rather than relying on a later working-tree version. Delivered notices and licences participate in the same complete map. There are no nested archives among these 851 members.

| Source | Delivery | Members | Existing upstream proposal |
|---|---|---:|---|
| 168 | `K215_Proof_Simplification_2026-10-21.zip` | 165 | [k215-simplification](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/README.md) |
| 169 | `K215_Proof_Transport_2026-10-21.zip` | 146 | [k215-transport](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-transport/README.md) |
| 170 | `Structural_Proof_Simplification_2026-10-21.zip` | 97 | [structural](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/structural/README.md) |
| 171 | `ZFC215_Proof_Simplification_2026-10-21.zip` | 187 | [zfc215-simplification](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc215-simplification/README.md) |
| 172 | `ZFC_K215_Proof_Transport_2026-10-21.zip` | 123 | [zfc-k215-transport](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc-k215-transport/README.md) |
| 173 | `zfc-fm215-proof-compression-2026-10-21.zip` | 133 | [fm215-compression](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/README.md) |

Recovery uses three explicit routes:

- **772 member occurrences** use exact immutable Git paths: 649 reference the upstream proposal placement, and 123 use pre-existing aliases checked at a named commit. Repeated payloads may share the same exact reference.
- **46 occurrences** use **41 new exact-byte ancillary files**, totalling **5,831,070 bytes**. These are 34 unique raw proof logs (39 occurrences; 5,597,022 unique bytes), three checksum records (26,571 bytes), and four original source files (207,477 bytes) whose bytes differ from the corresponding upstream placed blob. The two large historical `coqchk` logs account for most of this supplement; they have not been rerun.
- **33 occurrences** are read from their immutable arrival ZIP: the 22 main READMEs, manuscripts, PDFs and included manuscript inputs, plus 11 inert TeX-build artifacts. Exact upstream manuscript references remain recorded where present; this supplement does not copy them again. Every fallback has a reason in the map.

The four original source files are retained separately, without changing or normalizing either original or upstream version:

| Original Source-171 member suffix | Exact original bytes |
|---|---|
| `deps/K230/Prog230.v` | [07-Prog230.v](code/intake205-source171/07-Prog230.v) |
| `deps/K230/RM.v` | [08-RM.v](code/intake205-source171/08-RM.v) |
| `deps/K230/RMEquiv.rocq91.v` | [09-RMEquiv.rocq91.v](code/intake205-source171/09-RMEquiv.rocq91.v) |
| `deps/K230P/Bisim230.v` | [10-Bisim230.v](code/intake205-source171/10-Bisim230.v) |

Each of those map rows records both the original and upstream Git blob IDs. No inference about the cause of the byte difference is needed for exact recovery. Raw `.log` files and checksum records receive numbered `.txt` filenames so ordinary ignore rules do not discard this explicit supplement; their contents remain exactly as delivered. The map records all renames. Delivered code still contains its original relative paths and must not be executed from the rearranged ancillary layout.

The [own recovery helper](code/intake205-recover.py) reads each original ZIP and reconstructs each member from its selected route in memory, comparing the recovered bytes directly with the original member and the map. It never creates an output tree. From the repository root:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake205-recover.py --repo . --verify-only
```

The [actual recovery control](data/intake205-recovery-control.json) passes for all 851 members and rechecks all 41 supplemental files after the comparison. [Two negative controls](data/intake205-negative-controls.json) reject a changed member SHA and an omitted member. These controls exercise only our recovery helper; no delivered program, compiler, machine runtime or checksum-manifest verification is involved. Archive records carrying earlier compilation or runtime claims remain submitted evidence. This placement adds no formal theorem acceptance and does not modify the maintained K215 proof sources.

The original six ZIPs remain recoverable from arrival Git history even though upstream already removed their working-tree copies. A later written reconciliation can assess the mathematical proposals and current proof checkpoint separately. No historical placement record is rewritten here.

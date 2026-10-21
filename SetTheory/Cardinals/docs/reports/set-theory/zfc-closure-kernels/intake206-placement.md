# Batch 206 supplemental placement references: Source 174

Source 174 is supplementary reconciliation of **existing batch 206**. Its archive, `K215_Proof_Simplification_2026-10-21 (2).zip`, arrived in `53269bcab1efc0f82d3022645bd7cf0c22d84959` and was already placed and retired by `69e6d97fc2ea6da87b718109b1c8614a0927a621`. The [upstream proposal](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/README.md) remains the payload home. This supplement does not create another batch or another source-asset tree and does not retire a ZIP.

The [exact reference/recovery map](data/intake206-placement.json) covers all **360 regular members / 4,255,981 bytes**, including original names, sizes, SHA256 and Git blob IDs. References bind immutable commits and paths, not mutable working-tree aliases. Delivered notices and licenses are included. Main delivery prose and typeset manuscripts remain recoverable from arrival history, with existing upstream copies also recorded.

- **349 members** recover through immutable Git paths: 255 in the upstream proposal trees and 94 exact pre-existing aliases, including raw records in the committed batch205 supplement.
- **Six omitted raw proof logs**, totalling **2,130 bytes**, are retained unchanged in `data/intake206-source174/`.
- **Five members** use the arrival ZIP:four main manuscript/input members and one inert PDF-build log.

This revised delivery is distinct from batch205’s similarly named ZIP. Its source-proof and transport receipts remain delivered claims; the recovery operation does not rerun them, adopt a proof patch, or assert a new kernel-checked endpoint. There is no nested archive in this packet.

The [own recovery helper](code/intake206207-recover.py) reconstructs every member in memory from its selected route and compares it directly with the original ZIP member, its recorded size, SHA256 and Git blob. The [actual control](data/intake206-recovery-control.json) passes for the entire packet. The [four negative controls](data/intake206207-negative-controls.json) reject an omitted member and a changed member SHA for each batch. No output tree, delivered program, compiler, runtime, checksum-manifest suite or TeX build is involved.

From the repository root:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake206207-recover.py --repo . --map SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake206-placement.json --verify-only
```

The numbered `.txt` filenames retain raw log/checksum-record bytes despite ordinary ignore rules. All original relative paths remain in the map; delivered code is not intended to run from this rearranged ancillary layout. Any future selected replay requires a separately reviewed disposable reconstruction. A written reconciliation and catalogue update are separate follow-ups; this record changes neither queue status nor catalogue counts.

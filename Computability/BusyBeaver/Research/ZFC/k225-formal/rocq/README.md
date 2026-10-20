# Rocq endpoints for the 221- and 225-state candidates

## The 221

**Status: `PASS_CLOSED_KERNEL`** (2026-10-20). The endpoint is

```coq
K221F.CorrectDense221.tm221_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

Here `dense_tm` is the literal canonical table of
[candidate-k221](../../candidate-k221/README.md) (SHA-256 `6457dce8…`), the smallest known
candidate. The build counts both `Print Assumptions` reports of the final file, and both are
closed under the global context. `coqchk` then rechecked `K221F.CorrectDense221` independently
against Elliot Glazer's compiled K230 development (1,514 s).

The proof is a chain of equivalences:

| Step | Statement | Where |
| --- | --- | --- |
| dense table ↔ sparse table | the canonical numbering is a BFS order, so the dense-to-sparse map is an explicit 222-entry list (`dense_labels`), checked state by state | `Dense221` |
| TM ↔ register program | K230's TM side, with the nine deleted K230 labels (79, 140, 175, 191, 192, 208, 219, 226, 229) disabled; boot 409,835 steps | the runtime forks, `Sim230Main.tm230_rm` |
| the 221's source ↔ `dag222` | offset bisimulation, 2,247 entries, 8 offset, checked by `vm_compute` | `Source221.p221_dag222` |
| `dag222` ↔ enumerator ↔ calculus | Elliot's `ProgLib`/`L2Root` and enumerator layer, re-run on `dag222` | `Main222.dag222_iff_standardZFC` |
| calculus ↔ ZFC | soundness through Elliot's decoded K230 theory; completeness through K0 | `Sound222`, `Complete222` |

`dag222` is K230's `Dag230` with only the AX node rebuilt, so that it emits the merged
equality row G and the helper-free seed bundle. Elliot's program proofs went through unchanged
on it, which proves that the rebuilt word computes exactly the 222's enumerator step. The
calculus files and `dag222` come from [`../rocq224`](../rocq224/README.md) and are copied
under the namespace `K221F` by `regenerate221.py`.

| Path | Content |
| --- | --- |
| `rocq-extension/inputs/221/` | `table.tm` (byte for byte the canonical table), `table_k230labels.tm` (Source 132's K-labelled table, halt 254 renamed 230), `sites.json` (the 4,744-leaf rotated source), `Cert221Offsets.v` (from [`../gen_cert.py`](../gen_cert.py)) |
| `rocq-extension/regenerate221.py` | writes the 40 files of `coq/221/`: the 21 calculus and `dag222` files, the runtime forks, `Prog221`, `Source221`, `Table221`, `Dense221`, `Correct221`, `CorrectDense221` |
| [`add_variant221.py`](add_variant221.py) | registers the variant. In `build.py` it adds `--states 221`, and an explicit dense label list for tables whose canonical numbering is not the order-preserving compaction. In the manifest it adds the compile order, inputs and digests |
| `rocq-extension/receipts/kernel221/` | `verification.json`, `compilation.log`, `coqchk.log`, `toolchain.log` of the passing run |

The passing run took 2,555 s in all:

- compiling the 40 files took 1,041 s; the slowest were `Boot230` 387 s, `ProgLib222` 130 s,
  `Sim230` 64 s and `Interpreter230Check` 62 s;
- `coqchk` took the remaining 1,514 s.

```bash
python -B build.py --states 221 --reference <k230-rocq checkout> --jeff-reference <jeff-reference> --coqc <rocq 9.1.0>/bin/coqc
```

## The 225

**Status: `PASS_CLOSED_KERNEL`** (2026-10-19). The endpoint is

```coq
K225F.CorrectDense225.tm225_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

for the literal canonical table of [candidate-k225](../../candidate-k225/README.md)
(SHA-256 `f5d69a16…`). Its source is offset-bisimilar to K230's, so the rest of Elliot's chain
applies unchanged.

| Path | Content |
| --- | --- |
| `rocq-extension/inputs/225/` | `table.tm`, `table_k230labels.tm` (labels 79, 140, 175, 208 and 229 deleted), `sites.json` (5,121 leaves), `Cert225Offsets.v` (2,377 entries, 8 offset) |
| `rocq-extension/regenerate225.py` | writes the 19 `K225F` files of `coq/225/` |
| [`add_variant225.py`](add_variant225.py) | registered the variant in a fresh copy of Source 123's extension |
| `rocq-extension/receipts/kernel225/` | the receipts of the passing run |

The passing run compiled 19 files in 412 s, and `coqchk` took 1,093 s.

## What `rocq-extension/` is

The K226F extension of Source 123 (`K226_ZFC_Construction`, placed in the zfc-closure-kernels
host as `123-k226z-rocq-extension-*`), with the 225 and 221 variants added. The 226, 227 and 229
variants and their receipts are Source 123's, unchanged.

**On axioms.** `coqchk -o` lists every axiom present in the loaded environment. That is three
axioms (`inj_pair2`, `proof_irrelevance`, `eq_rect_eq`), declared by BusyCoq's `LibTactics.v`,
which Elliot's development loads. The 225's and 221's checks list the same three. Neither final
theorem depends on them: its `Print Assumptions` reports are closed, as Elliot's own README
explains for K230. The checks report no unsafe fixpoints and no assumed positivity. (An earlier
version of this page said the 225's check "reports no axioms"; it lists those three, like the
221's.)

## Building Rocq 9.1.0 on Windows

`toolchain/` records how the pinned toolchain (Rocq 9.1.0, OCaml 4.14.2, rocq-stdlib 9.0.0) was
built on this machine. Rocq 9.1.0 has no opam package for the existing switch here, and creating
a new switch failed. So the build goes from source into a private prefix, reusing the OCaml
4.14.2 of the opam switch `rocq-9.2`, which stays untouched. Notes:

- Run the scripts under opam's Cygwin bash. Git Bash rewrites `/cygdrive` paths.
- Keep every path under 260 characters; the build goes through a `subst` drive.
- `build.py` wants the reference, the extension and the compiler on one drive. Give it the real
  `C:` paths, and set `ROCQLIB`/`COQLIB` to the stdlib's `C:` path.
- `dune build -p rocq-core` alone fails after the dunestrap step. Build
  `-p rocq-runtime,coq-core,rocq-core` together (`resume_rocq910.sh`).

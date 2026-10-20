# Rocq endpoint for the 225-state candidate

**Status: `PASS_CLOSED_KERNEL`** (2026-10-19). The endpoint is

```coq
K225F.CorrectDense225.tm225_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

Here `dense_tm` is the literal canonical table of
[candidate-k225](../../candidate-k225/README.md) (SHA-256 `f5d69a16…`). It is closed under the
global context (the build counts both `Print Assumptions` reports), and `coqchk` independently
rechecked `K225F.CorrectDense225` against Elliot Glazer's compiled K230 development.

## What is here

`rocq-extension/` is the K226F extension of Source 123 (`K226_ZFC_Construction`, placed in the
zfc-closure-kernels host as `123-k226z-rocq-extension-*`) with a fourth variant, 225, added:

| Path | Content |
| --- | --- |
| `inputs/225/` | `table.tm` (byte for byte the canonical dense table), `table_k230labels.tm` (the same machine in K230 labels; labels 79, 140, 175, 208 and 229 deleted), `sites.json` (the 5,121-leaf source), `Cert225Offsets.v` (the offset certificate written by [`../gen_cert.py`](../gen_cert.py): 2,377 entries, 8 of them with register 5 offset by one) |
| `regenerate225.py` | writes `coq/225/` from the K230 reference and the inputs; the dense-to-sparse expansion is generated from the deleted-label list, and on Source 123's own case it reproduces that source's map |
| `coq/225/` | the 19 `K225F` files: runtime forks of K230's TM side with the deleted labels disabled, `Prog225`, `OffsetBisim230`, `Cert225Offsets`, `Source225` (p225 ↔ p230 by `vm_compute`), `Table225`, `Dense225`, `Correct225`, `CorrectDense225` |
| `build.py`, `manifest.json` | Source 123's builder, with `--states 225` added; the manifest registers the variant (namespace `K225F`, target `CorrectDense225`, 2 expected closed reports, boot 409,835 steps) |
| `receipts/kernel225/` | `verification.json`, `compilation.log`, `coqchk.log`, `toolchain.log` of the passing run |

[`add_variant225.py`](add_variant225.py) is the script that registered the variant in a fresh
copy of Source 123's extension. The 226, 227 and 229 variants and their receipts are Source 123's,
unchanged.

## The passing run

- Toolchain: Rocq 9.1.0 (OCaml 4.14.2) with rocq-stdlib 9.0.0, the versions k230-rocq pins.
- Reference: k230-rocq at `3142e4d`, built and `coqchk`-checked first with its own `build.py`
  (692 s).
- Extension: 19 files compiled in 412 s (`Boot230` 198 s, `Sim230` 56 s, `Interpreter230Sites`
  38 s, `Interpreter230Check` 34 s). `coqchk` of `K225F.CorrectDense225` took 1,093 s and reports
  no axioms, no unsafe fixpoints and no assumed positivity.

Reproduce:

```bash
python -B build.py --states 225 --reference <k230-rocq checkout> --jeff-reference <jeff-reference> --coqc <rocq 9.1.0>/bin/coqc
```

## Building Rocq 9.1.0 on Windows

`toolchain/` records how the pinned toolchain was built on this machine. Rocq 9.1.0 has no opam
package for the existing switch here, and creating a new switch failed, so the build goes from
source into a private prefix, reusing the OCaml 4.14.2 of the opam switch `rocq-9.2` (which stays
untouched). Notes:

- Run the scripts under opam's Cygwin bash. Git Bash rewrites `/cygdrive` paths.
- Keep every path under 260 characters. The build goes through a `subst` drive. `build.py` wants
  the reference, the extension and the compiler on one drive, so give it the real `C:` paths and
  set `ROCQLIB`/`COQLIB` to the stdlib's `C:` path.
- `dune build -p rocq-core` alone fails after the dunestrap step. Build
  `-p rocq-runtime,coq-core,rocq-core` together (`resume_rocq910.sh`).

# Normalized K215 source-correspondence proof

This module set is for ProveIt commit
`b6c7087477e51c017003bd729e712c8969733223` and Lean **4.32.0**.
It reduces the pinned 2,240-entry source certificate to **1,426 entries** by
identifying finite instruction pointers with the same implicit trailing-zero
extension. Both source programs and the 215-state machine remain identical.

The new generic checker is `RMNormalizedBisim.lean`. Its 161 lines reuse the
existing segment-bisimulation theorem. `normalized_lean/KSource215.lean`
exports the same public theorem name and statement as the pinned module:

```lean
KSource215.p215_halts_iff (R : Registers) :
  Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩
```

See `research_note.md` for the mathematics, source references, and precise
scope. `normalized_summary.json` records finite certificate statistics;
`kernel_receipt.json` records the actual checked status and compiler output.
A Python checker is useful for debugging but is outside the proof's trust base.

## Reproduce the kernel checks

From this directory, with a checkout at the pinned commit:

```sh
python3 verify_lean.py --repo /path/to/ProveIt \
  --lean /path/to/lean-4.32.0-linux/bin/lean \
  --build /path/to/empty-normalized-build
```

The output directory must be absent or empty. The driver checks the repository
commit and the SHA-256 hashes of all eight imported upstream source modules,
then compiles the entire minimal dependency chain serially in a separate
module tree. It writes a new `kernel_receipt.json` and compiler logs under the
chosen build directory; it does not overwrite the shipped evidence or edit
the checkout. Default per-process memory limit is 3,500 MB. No Mathlib or
network access is needed after obtaining Lean and the pinned checkout.

## Regenerate the untrusted certificate and Lean declarations

```sh
python3 normalize_certificate.py
python3 render_programs.py
python3 render_shared_trees.py
python3 render_normalized_lean.py
```

`upstream/sites215.json`, `upstream/dagperm_nodes.json`,
`upstream/gen_cert.py`, and `upstream/KSource215Data.lean` preserve the pinned
input data and source. Input hashes are recorded in the normalized certificate.
The generator checks all 1,425 decrement sites, the sole halt site, both
successors at every decrement, and the initial segment. It also emits
`old_to_normalized.json`: a surjective map from the original certificate that
preserves both successors. Regeneration resets the summary's kernel-status
flag; run the Lean checker for the regenerated files.

## Integration

Copy `RMNormalizedBisim.lean` and `normalized_lean/*.lean` into the repository's
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC` directory, preserving filenames.
The new `KSource215.lean` and `KSource215Data.lean` replace those modules at the
same public namespace. The remaining files are added modules. Update build
module registration if the surrounding build system explicitly lists modules.
The public definitions `p215`, `pathDagPerm`, `path_iff_iter`, `t215`, `tD`, and
`p215_halts_iff` are retained. The finite certificate representation is private
to this source-correspondence proof; callers should use the public theorem.

This deliverable proves the exact all-register source correspondence. It does
not claim a fresh build of the complete machine-to-consistency endpoint, and
it does not reduce the machine's state count. The proposed analogous Rocq
normalization remains a porting task; no Rocq source-checker instance is
claimed here.

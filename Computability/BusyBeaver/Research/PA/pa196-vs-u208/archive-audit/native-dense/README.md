# Dense/native PA196 conjugacy in Lean

The imported PA196 machine has a dense presentation, with working states
`0..195`, start 0 and halt 196, and a sparse native presentation, with start
74 and halt 254. These are **the same machine under a state relabeling**, not
two distinct consistency-machine constructions. This directory proves their
standard-natural-number blank-tape halting and nonhalting equivalence in Lean.
It does **not** prove any sentence inside iPRA or the PA consistency
calibration for either presentation.

[NativeDense/Core.lean](NativeDense/Core.lean) contains the same list-zipper
tape and step definitions as the imported `M6/Zip.lean`. Its constructive
generic simulation theorem relates every finite run using positive state
bounds and row conjugacy. `Halts` means that some execution prefix is `none`;
`halts_iff_reach_and_stop` proves this equivalent to the imported zipper's
formulation of reaching a configuration with no transition. Neither transport
uses excluded middle as a logical hypothesis.

[NativeDense/Tables.lean](NativeDense/Tables.lean) is generated from the exact
bodies of the imported `PA196/Literal.lean` and `PA196/Table.lean`, changing
only the definition names and the type alias name. The 197-entry state map is
extracted from the imported `PA196/Conjugacy.lean`. Its Lean theorems include:

- `exact_rows` and `rows_conjugate`: every pair of a working or halting dense
  control and a Boolean tape symbol has the corresponding native action;
- `next_bounded`, `labels_nodup`, `starts`, and `halts`: finite table and label
  facts used to bind the simulation;
- `dense_native_halts_iff`, `dense_native_reach_and_stop_iff`, and
  `dense_native_nonhalting_iff`: closed blank-input transport statements,
  with no remaining row-agreement assumption.

All finite row checks use `by decide`, split into 13 batches to limit kernel
memory. No `sorry`, `native_decide`, or custom axiom is used. `#print axioms`
reports `propext` for the row check and `propext`, `Quot.sound` for the
transport theorems. These are standalone copies of the upstream definitions,
not imports of the upstream Lean 4.35 modules into Lean 4.32.

[generate.py](generate.py) pins all three upstream Lean files, the exact dense
`.tm` data and the native `.tm` member of `pa_consistency_research.zip`. It
independently interprets the pinned source transition trees and compares all
392 dense and 392 native rows with those data, then regenerates the Lean file
byte for byte. The latter input/provenance check is Python evidence, not a
Lean proof about ZIP bytes. Source and data hashes are recorded in that script.

From the repository root, with Python 3 and Lean 4.32.0:

```sh
bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/native-dense/check.sh
```

The checker writes only to a private temporary directory and removes its own
outputs. The accompanying [license](LICENSE.JamesChang) retains the upstream
MIT notice. Upstream authors have not reviewed this standalone port.

To use this relationship for the requested iPRA endpoint, the zipper machines
and renaming still need to be connected to the selected first-order iPRA
halting formulas, and their finite-trace transport proved in iPRA. Other
196-state candidates with genuinely different rooted graphs need additional
simulation theorems; this relabeling theorem does not cover them.

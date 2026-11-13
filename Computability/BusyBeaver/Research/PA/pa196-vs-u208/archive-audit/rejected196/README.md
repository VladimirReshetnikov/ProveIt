# Two rejected 196-state tables halt on blank tape

The archive `docs/incoming/conpa_tm_comparison_and_reduction_search.zip`
contains two **explicitly rejected** 196-working-state tables:

- `rejected/REJECTED_shift_layout.tm`, SHA-256
  `db5cd7df1475e4c2edf43f856493e211ed116a7a998eaada741515840424736b`;
- `rejected/REJECTED_combined_layout.tm`, SHA-256
  `d3a049def261732d1c1aa99a48de63c00a1241f02b629b2ae45d445bba6c9527`.

They have dense working labels 0–195, blank-start state 0, and distinct halt
label 196. They differ in exactly one row, `115/1`; their common blank run
never visits that row. Both first enter state 196 at step **43,563**. These
are rejected experiments, not consistency machines. Their presence matters
when interpreting a request to cover machines in incoming archives: not every
196-state-table experiment in an archive is intended to satisfy the consistency
property.

## Lean certificate

[Cert/Common.lean](Cert/Common.lean) defines a two-natural-number tape: the
low bit of the right number is the scanned cell and the low bit of the left
number is the neighboring left cell. A right move writes and shifts the right
head bit onto the left stack; a left move performs the inverse tape update.
The literal 392-row array is the first archive table; a Boolean selects the
other table's unique changed row. State 196 is made absorbing after halt, which
is convenient for the iteration and does not change the first halt time.

The `safeRun` computation rejects any visit to the differing row.
[Cert/Batch0.lean](Cert/Batch0.lean) through `Batch17.lean` contain 171
kernel-checked chunks, each of at most 256 steps. Their endpoints form one
continuous trace from blank input. [Cert/Before.lean](Cert/Before.lean)
checks the penultimate state. [Cert/Final.lean](Cert/Final.lean) composes the
chunks, proves that the safe trace transfers to both tables, and proves:

- `rejected_shift_reaches_halt` and `rejected_combined_reaches_halt`:
  both runs have control 196 at step 43,563;
- `not_halted_before`: for both tables, every earlier step has control
  different from 196.

The chunk proofs use `by decide`, not `native_decide`, `sorry`, or a custom
axiom. `#print axioms` for the final theorems reports `propext` and
`Quot.sound` from the composition lemmas. This is a Lean theorem about the
explicit standard-natural-number transition model. It is **not** a formal
sentence or proof inside iPRA, a formalized archive-byte parser, or a proof
about PA consistency.

[check_inputs.py](check_inputs.py) independently checks the ZIP and member
hashes, verifies that Lean's inline table matches the archive, and replays the
same checkpoints and unique changed row. This Python binding supplies
provenance evidence; it is not part of the Lean kernel proof. The ZIP hash is
`46cd1a5f57f6c04f9a0379fa8dc042120bc6ae0329c370ca5d4a3d35907b5d48`.

From the repository root, with Python 3 and Lean 4.32.0 installed:

```sh
bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/rejected196/check.sh
```

The script creates a private temporary directory, compiles the common model,
penultimate checkpoint, and batches with three parallel jobs by default, then
checks the final theorem. Set `PA196_REJECT_JOBS=1` for sequential execution.
It deletes its own temporary outputs on exit and does not download dependencies.

The table descends from James Chang's PA196 machine; its retained
[MIT license](LICENSE.JamesChang) accompanies this derived representation.
The archive supplies the rejected experimental changes and their provenance;
neither the upstream author nor the archive authors reviewed this certificate.

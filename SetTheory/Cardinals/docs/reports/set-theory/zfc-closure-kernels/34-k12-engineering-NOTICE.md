# Attribution and source boundaries

The contiguous-counter construction, its shared-cleanup adaptation, the
integer optimization proof, this reproducible experiment, and its quotient
certificates were prepared by ChatGPT for Vladimir Reshetnikov on
16 October 2026. The general transition-homomorphism method is standard and
already has a generic theorem in ProveIt's `StateReduction.lean`; it is not
claimed as a new theorem of automata theory.

The copied ProveIt modules are unchanged from the reviewed source at
`d74c63b0c8d4f35597f1bd5976d941b9f104f94e`:

- `Computability/BusyBeaver/Research/ZFC/mira_backend.py`
- `Computability/BusyBeaver/Research/ZFC/compact_initializer.py`
- `Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py`

The existing compact initializer is source21 of the closure-kernel report
intake, incorporated in batch150. Its original notice remains in the minimal
snapshot. We compare to its existing counts and do not attribute that
construction to the present work. The 206-node full-logic DAG is the preserved
source19 selected control; the 202-node DAG is the preserved source09 decoder
control as shipped with source20. The original source19 notice is retained.
ProveIt's and Cardinals' existing MIT No Attribution license files are retained.

The finite 219-node program and original literal 254-state table are copied
unchanged from `jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. Mira-Cult designed the machine,
compact calculus, and source program; Jeff supplied the published verification
and finite numeric data. Andrew James Wade supplied the compiler framework.
The upstream M254 and generator README files and Wade's MIT-0 notice are retained.
No blanket relicensing of finite upstream machine/program data is asserted.

The public 253-state table is the identical finite artifact preserved in
ProveIt source04 and published in mira-emmy's PR20 at
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. Its original file SHA256 is
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
The reduction and its verification are attributed to their existing authors;
the present package merely confirms that ordinary exact partition refinement
finds no additional state identification in that table.

All input and output hashes are recorded in `results/evidence.json`. Vendored
code is not changed or executed as Coq. The Python compiler is executed as
documented in ProveIt; the `.v` program is parsed only as finite input data.
The local package supplies no new Coq/Lean kernel certificate and does not
claim a new ZFC-consistency state record.

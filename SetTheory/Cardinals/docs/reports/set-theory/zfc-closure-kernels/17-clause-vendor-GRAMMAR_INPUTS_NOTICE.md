# Minimal source inputs for the full-word grammar comparison

The files listed in `data/full_grammar/pinned_inputs.json` are copied
byte-for-byte from the audited incoming
`docs/incoming/zfc_small_machines_20261016.zip` at ProveIt commit
`47f3a3602946dfe48803a91a910c646e74637ac8`. This is a deliberately partial
source snapshot, not a complete repository or formal proof development.

## ProveIt helpers

The files `recover_wade_dag.py`, `theory_backend_experiment.py`, and
`pairing_backend_experiment.py` retain their original path below
`ProveIt/Computability/BusyBeaver/Research/ZFC/`. Their original source pin is
`17d0f2eaa650901cda59764dfcc4661c199e49c8` in
https://github.com/VladimirReshetnikov/ProveIt .
`ProveIt/LICENSE` is the unmodified MIT No Attribution license from that
source package. This license is not presented as relicensing unrelated
third-party inputs.

## Published program and Wade backend

Below `ProveIt/lib/jeff-busy-beaver-zfc254/` the original paths are retained
for the three Python backend modules, their `LICENSE.wade`, `Dag254.v`,
and `tools/logic/spec.py`. The source repository is
https://github.com/jeff87654/busy-beaver and the exact upstream pin is
`297ab8df7e5de329605c3875b4934643b371a5e3`.

Andrew James Wade wrote the backend; its original MIT No Attribution
license is retained unchanged. Mira-Cult designed the original machine,
source program, logical calculus and nonextensional theory. Jeff published
the Coq verification and numeric program used here. The `.v` file is parsed
as finite DAG data, not compiled as a Coq development. Only pure symbolic
definitions are selected from `spec.py` by AST; its original numeric
enumerator and external `bignum` dependency are not executed.

## Source-08 grammar helpers

`one_schema_machine/rebracket_axioms.py` and
`one_schema_machine/verify_rm_certificate.py` originate in
`zfc_one_schema_research/machine/` inside ProveIt's incoming
`docs/incoming/zfc_one_schema_research.zip`, introduced at commit
`39409c8c921cccdbd6162c8767c84cfb7df65df1`. The archive's original notice is
retained unchanged as `one_schema_machine/ORIGINAL_NOTICE.txt`; its paths
refer to that original archive layout.

The present package does not assign new authorship to the grammar method,
independent RM checker, upstream machine or backend. The new
`code/search_full_grammar.py` is only a bounded experiment driver using these
existing interfaces. No additional license grant or blanket relicensing of
third-party inputs is implied.

The exact offline commands and model caveats appear in
`data/full_grammar/README.md`.

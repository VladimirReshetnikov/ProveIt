# Optional experiment attribution and license boundary

All imported inputs are pinned to
[`VladimirReshetnikov/ProveIt` commit `43026ff42f0939f09b9e95495248cfadcad38e38`](https://github.com/VladimirReshetnikov/ProveIt/tree/43026ff42f0939f09b9e95495248cfadcad38e38).
The payload inventory gives SHA-256 values for the exact archived bytes;
`imported_fixtures.json` also gives the corresponding repository paths and
Git blob identities. Copies with different local paths are listed explicitly.

## Machine, literal source program, and verification

Mira-Cult designed and built the original 254-state machine, its compact
calculus, and its single-marker interpreter. Jeff (`jeff87654`) supplied the
published Coq verification. Andrew James Wade supplied the public compiler
framework used by predecessor research. Mira-emmy supplied the public
253-state reduction, and the pinned ProveIt work supplies the permutation252
baseline. The current cache-MP transformation and new experimental drivers
build on this work; they do not claim authorship of those predecessors.

The exact imported `Dag254.v` and `Prog254.v` originate in
[`jeff87654/busy-beaver` commit `297ab8df7e5de329605c3875b4934643b371a5e3`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3),
at `ZF/m254/coq/prog/Dag254.v` and `ZF/m254/coq/tm/Prog254.v`. They are included
as finite source tables, with all original content preserved. Their exact
upstream README is retained as
`workspace/sources/attribution/README.jeff-m254.md`. The ProveIt snapshot's
unchanged provenance and license-boundary notice is
`workspace/sources/attribution/README.proveit.md`.

That notice states that the pinned upstream `busy-beaver` tree declares no
upstream-wide license and that its imported snapshot is excluded from
ProveIt's blanket MIT-0 grant. This package preserves that boundary and does
not add a license grant for the upstream table or sources. Upstream README
claims describe the upstream verification, not a local Coq or Lean build of
this research package.

## Imported experimental helper files

`agents/machine_reduction/decoder_entries.json` is the exact pinned file
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/27-variant-experiments-machine_search-grammar_search-decoder_entries.json`.
Its entries are context-sensitive emitter hints, as its own warning states.
It is not independently a runtime proof.

The imported affine helper is the exact pinned
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py`.
The new rotation drivers also acknowledge the source09 closed-region rotation
and source27 contextual-subtree emitter methods. No separate license notice
was identified for these retained delivery fixtures; this package preserves
their attribution without inventing a grant. The pinned reconciliation is
[the closure-kernel intake README](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md).

The imported ProveIt helpers `candidate252_independent_audit.py`,
`permutation252_spare_fold_search.py`, `breakthrough_register_permutation.py`,
and `safe_seed254.py` retain their authorship and source documentation. The
first three are byte-identical to their pinned files. The local research
copy of `safe_seed254.py` has one extra trailing LF relative to its upstream
blob and otherwise has identical bytes; that harmless formatting difference
is explicitly recorded and retained, so the original research input is not
silently normalized. Copies of the pinned old-label machine and its README
retain the same baseline attribution.

`workspace/sources/attribution/LICENSE` is the exact ProveIt root
MIT No Attribution license, copyright 2026 ProveIt Contributors. It is
retained for the ProveIt-authored material to which it applies, and does not
override the upstream exclusions above. No Wade backend module, vendored
busycoq implementation, or Coq Library of Undecidability Proofs module is
included in this optional workspace, so their unrelated license files are
not presented as licenses for this payload.

## New experimental evidence

The newly written cache-MP experiments, search ledgers, compilation outputs,
and packaging notes were produced for this research on 17 October 2026. They
retain the original working labels and predecessor provenance. Their
mathematical and verification limits are described in `REPRODUCE.md` and the
main report. Input files and historical result records have not been edited
to conceal failed or partial searches.

# Attribution and source boundaries

This research package was prepared for Vladimir Reshetnikov's request on
16 October 2026. It contains a research synthesis, an alternative mathematical
proof, exact audit witnesses, a reference checker/enumerator, and compiler
experiments. It does not assign new authorship to the pre-existing theory,
machines, code or proof developments discussed below.

## Mathematical predecessors

The ProveIt closure-kernel submissions and repository research establish the
background PSC and subset-bound constructions. In particular **batch 144
source 08**, `zfc_one_schema_research.zip`, supplies the already accepted
ordinary equality-free PSC-only consistency calibration, hereditary
saturation, the purity cut, and transfer to the extensional PSC theory.
Its original arrival is commit
`39409c8c921cccdbd6162c8767c84cfb7df65df1`.

The main report independently develops an incoming-profile-fragment /
nonempty-monochromatic bootstrap, adopts source 08's purity cut with credit,
and directly derives the interpreted ZF axioms. No historical novelty or
minimality claim is made for PSC-only equiconsistency or hereditary saturation.
The underlying hereditary interpretation idea also appears in Al-Johar's
nonextensional replacement discussion, as credited in source 08.

## Existing machines and proofs

Mira-Cult designed the original 254-state machine and its source program.
Jeff (`jeff87654`) supplies the upstream formal verification. The 253-state
reduction is the mira-emmy contribution in upstream pull request 20, exact
head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

The exact 253/254 `.tm` tables are retained as attributed benchmarks.
`code/verify_benchmarks.py` is copied unchanged from the incoming archive
`zfc_machine_research.zip` at ProveIt commit
`17d0f2eaa650901cda59764dfcc4661c199e49c8`; it was independently rerun.
The existing normalized equality-free 252-state candidate is copied unchanged
from that ProveIt snapshot and is explicitly labeled uncalibrated.

## Formula generator

`code/qpsc_syntax.py` is adapted from `code/syntax.py` in the incoming
`zfc_tm_pure_subset_research.zip` at the same ProveIt snapshot. Its original
source and authorship remain attributed to that research submission. An
attribution header was added; its equality-free closure construction is used
by the new tableau reference. The optional equality helpers in that module
are not accepted executable syntax by the tableau's public parser.

## Compiler dependencies

The following nine files in `reference_sources/proveit/` are copied
byte-for-byte with their original relative paths:

- ProveIt's `theory_backend_experiment.py`, `recover_wade_dag.py` and
  `pairing_backend_experiment.py` at the pinned compiler snapshot.
- Andrew James Wade's `TMBuilder.py`, `tm.py`, `tmdb.py` and `LICENSE.wade`
  from upstream `297ab8df7e5de329605c3875b4934643b371a5e3`.
- The upstream `ZF/m254/coq/prog/Dag254.v` finite register program and
  `ZF/m254/tools/logic/spec.py` symbolic logical specification.

The Wade files retain their **MIT No Attribution** license in the exact
original `LICENSE.wade` file. The ProveIt/upstream research notices distinguish
the licensed backend from other third-party materials without a blanket
upstream-wide license. This package does not relicense any third-party code,
machine table or proof source. Only the small dependency closure needed for
the requested research reproduction is included; the full upstream Rocq
development is not redistributed.

The new audit scripts, reference tableau/enumerator, measured controls and
report are prepared for this task. Their tests are finite executable evidence;
they do not replace the cited formal or ordinary mathematical proofs.

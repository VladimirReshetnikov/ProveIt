# Source provenance

The pinned ProveIt revision is
`3268f238cb6be4b9c68b6cddaf289f173f77566e`.

`inputs/Program.lean` is the unmodified source DAG imported in
`Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean`.
Its upstream source is James Chang's `jamesyc/BusyBeaver` revision
`407cdc356f6b586635e71ac92be394255f4bfea4`. Its SHA-256 is
`8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872`.
The original MIT license is retained in `LICENSE.JamesChang`.

`source_core.py` adapts the parser, tree operations, metrics, and source CFG
resolver from ProveIt's
`Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/scan_rotations.py`.
Its input path is changed to the bundled source, and the command-line search
driver is omitted. ProveIt's license is retained in `LICENSE.ProveIt`.

`inputs/base_config.json` is the inherited two-orientation AX configuration
from member
`pa_tm_extended_research_2026-11-13/experiments/config.json` of
`docs/incoming/pa_tm_extended_research_2026-11-13.zip`.
It is retained solely as an exact baseline identity control.

The new gate spellings, membership-transposed configurations, local direct
pairing macro and its ordinary proof, exact transposed-implication prefix,
orientation lemmas and guard counterexample, and first-head countermodel were
developed during this task. They preserve the distinction between mathematical
source reasoning, finite transcription checks, and missing binary/internal-PA
verification.

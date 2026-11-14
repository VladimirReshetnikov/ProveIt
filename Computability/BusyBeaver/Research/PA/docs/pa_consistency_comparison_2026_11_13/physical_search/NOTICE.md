# Provenance and scope

The frozen literal table, program tree, and state-label map are copied from James Chang's `jamesyc/BusyBeaver` at commit `407cdc356f6b586635e71ac92be394255f4bfea4`. Its MIT notice is retained in `LICENSE.JamesChang`.

The unchanged `verification/symbolic.py` comes from `docs/incoming/pa_consistency_research_2026-11-13.zip`, member `pa_consistency_research/verification/symbolic.py`, in Vladimir Reshetnikov's ProveIt repository, observed at commit `dc523e7b06ffb414093c90aa035500ca283e5f75`. Its header identifies it as a Python port of the M6 symbolic runtime. This package retains its source header and does not claim that the original authors reviewed or endorsed the new experiments.

`fold_two_general.cpp` adapts `Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-row/scan_two_rows.cpp` from the same ProveIt snapshot. The changes make the window radius configurable and raise the new-block limit to 64 transitions. `LICENSE.ProveIt` retains the repository's MIT No Attribution license notice. The other search and packaging scripts in this subpackage were written for this report. No notice here overrides an inherited file's license.

The source-derived window argument is not a new theorem in the supplied Lean development. The Python interpreter uses previously established engine contracts as an oracle; the C++ programs enumerate finite templates. These distinctions are essential when interpreting the receipts. No smaller verified TM or PA-internal equivalence was obtained by these searches.

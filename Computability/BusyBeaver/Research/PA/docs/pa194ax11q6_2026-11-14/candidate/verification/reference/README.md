# Origin of the independent symbolic checker

The four files in this directory were copied byte for byte from:

`docs/incoming/PA195_ConPA_research_2026-11-14.zip`

at ProveIt commit `5ed5a41fa5932433111eea096311364c6087e8e3`, under member prefix:

`pa_consistency_research/physical195_audit/reference/`

They are `symbolic_runtime.py`, `independent_runtime.py`, `source_language.py`, and `legacy_mapping.json`. The supplied comments credit the earlier U214 whole-tape symbolic induction engine and K225/K226 source-language tools. The present wrapper sets the proved header base to 48 and selects the appropriate physical register map; it does not change the inherited symbolic execution rules. The legacy state map only renames controls to the four generic list-lemma entry labels. Each list lemma is then proved again against the literal candidate table.

The relevant supplied licenses are retained beside these files. This wrapper and the machine changes do not relicense the imported work.

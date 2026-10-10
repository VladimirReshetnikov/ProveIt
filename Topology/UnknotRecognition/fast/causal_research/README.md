# Native bounded Pachner search

The transport, commitments, region, causal and shared-cover modules are integrated from report 79 (`reports/79/repro/fast/fastunknot/`). Existing 2–3/3–2 move producers, their independent checkers, the cocycle kernel and integer codec were byte-identical to that snapshot. The delivered report and its evidence remain unchanged.

`pachner_cover_search.find_pachner_descent` decides the bounded total-upward descent question when its complete connected cover family is exhausted. Default connected radius is `min(t,3U+3)`. Caps are inconclusive; no bounded exhaustion is a knot verdict.

`normal_pachner_search.pachner_seed_decide` binds verified transported disc witnesses to the input diagram. For bounded-region sleep/naive searches, it probes the source endpoint first, then uses the shared cover engine after a miss, with a shared node/work allowance. `recognize(..., use_pachner_seed=True)` and `--pachner-seed` enable this optional stage. It defaults off.

The fixture, commitment fixture and transport splitting modules are retained from the same source package. Tests referencing historical retained endpoints read the immutable report artifacts directly.

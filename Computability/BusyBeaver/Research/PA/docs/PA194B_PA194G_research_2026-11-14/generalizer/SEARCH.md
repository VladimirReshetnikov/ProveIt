# Discovery and unsuccessful reductions

This search log accompanies PA194G, a verified new 194-state realization.
No verified machine with fewer than 194 working states was obtained.
These runs are discovery heuristics, not a state lower bound.

## Source searches

All numerical scores use a fixed term of 134 controls plus the number of
AX reader states minus a syntactic helper-matching score. A low score is
only a candidate: physical compatibility still has to be checked. The
shipped PA194G was separately built and fully verified with an actual
compatible seven-fold set. Iteration slots count the main stochastic loop.
Evaluations additionally include initial seed scoring and restart/repair
proposals; skipped slots count proposals that could not be reassociated.
Thus evaluations and skipped slots are not a partition of iteration slots.

* A baseline source/association search used seed 918230141 and 5,000,000
  iteration slots: 4,397,849 score evaluations and 604,569 skipped slots.
  Best effective reader score was 60, hence candidate total 194. Alternative
  guarded source variants had best scores 63, 64, and 66.
* A final-stack zero-copy search used seed 202611141314 and 10,000,000
  slots: 8,787,951 evaluations and 1,215,736 skipped slots. It explored
  equivalent zero sources alongside the AX source associations. Every
  source family retained best score 60; no lower score was found.
* A logical-source search explored exchanged membership premises and
  equality orientation using seed 73596217 and 15,000,000 iteration slots:
  13,185,323 evaluations and 1,819,822 skipped slots. The best effective
  reader score was 60; the alternative source-family minima were 67, 65,
  and 67. These were possible lower-state sources; no new completeness
  theorem was assumed from a promising score.
* A diagonal-head argument search Gamma(A/H/D) used seed 829552309 and
  15,000,000 slots: 13,165,875 evaluations and 1,838,659 skipped slots.
  Its best effective reader scores were 62, 64, and 60 respectively.
  Thus the cached-zero baseline with Gamma(D) remained the best candidate;
  no smaller source score was found.

The C++ sources and their complete frozen input arrays are in `search/`.
They use only the C++ standard library. To replay a run, from the selected
subdirectory use:

    g++ -O3 -std=c++17 source_search.cpp -o source_search
    ./source_search ITERATION_SLOTS SEED output_prefix

Budgets and seeds are given above or in the corresponding JSON receipt;
full runs can take several
minutes. The binary executable is intentionally not required by the
construction or its verification.

Across these four stochastic runs the budget was 45,000,000 main-loop
slots, with 39,536,998 score evaluations including initialization and
restart/repair candidates. Full run receipts and retained best source
witnesses are included in `search/`.

## Generalization protocol search

The decisive change is to the AX parameter source of the saved universal
formula: `U(d,h)` becomes `U(c,h)`. I screened 1,233 distinct archived
190-token source associations after this change. The complete scored
records are `search/generalizer_screen.json`, with repository-relative
source paths. The best projected total was 194, using the association
originally stored as

    PA/docs/pa194qh6_conpa_2026-11-13/research/grammar/qh6.seed9.grammar.json

The immutable grammar actually used is `grammar.json`. The initial
maximum matching selected an incompatible contextual fold. Enumerating
compatible seven-fold choices produced the checked `folds.json`; all 28
simultaneous local cases then passed. Every source outcome and whole-tape
startup was subsequently checked by two symbolic engines.

The archived association is reused, but its command word and mathematical
interface are changed. The new compiler's Gen_i word saves one offset
command. The complete new proof and source binding are in `proof.tex`,
`check_commands.py`, and `build.py`; the final literal table is distinct
from all 82 prior 194-state graphs in the supplied corpus.

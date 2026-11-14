BOUNDED GRAMMAR SEARCH

This directory records the final corrected heuristic search, including its
source and two initial grammars. Run from this directory with Python 3:

    python3 anneal.py

The declared budget is 160 cycles of 1,600 attempted rotation proposals.
A proposal with no applicable rotation is skipped. The objective is the
number of allocated AX readers less the largest compatible selected set of
context folds, plus explicit address/marker/context penalties. The fixed
physical contribution is 134 working controls. Thus cost 62 corresponds to
196 working controls when all penalties vanish.

Both binary trees (incT, incT) and ((incT, incT), (incT, incT)) reuse existing
native controls 99 and 190. The compatibility search enumerates all
available helper choices for every selected fold row. It checks the final
simultaneous patched table, including aliases, on each admissible two-cell
local context. Every proposed cost of at most 61 triggers the full source
instruction-contract checker before a candidate table is exported.

This is a bounded heuristic experiment, not an exhaustive search over all
binary trees or all machines. The pseudorandom numerical seed is explicit;
Python set iteration also affects proposal order, and PYTHONHASHSEED was not
fixed for the recorded run. Re-running the program need not reproduce the
same trajectory. Exact reproduction of the two supplied machine tables is
provided by ../verify.py and is independent of this search.

The supplied final log records the actual completed scope. The original
fixed-control reuse screen was a separate deterministic check of the first
96 saved cost-62 grammar ties. It found no local candidate; its log and code
are also retained, together with the 96 exact input grammars and their input
manifest. Run python3 fixed_reuse_screen.py to repeat that finite screen.
The saved ties were exploratory associations of the two
seed emitter words, not additional claimed machine constructions.

SCANNER LAYOUT EXPERIMENT

A separate 30-cycle, 1,000-proposal-per-cycle bounded portfolio minimized
internal AX addresses obstructing the proposed shorter origin scanner. It
started from the ten best scanner scores among the saved cost-62 ties and
finished with six internal obstructions. The fixed exterior node164 rotation
was then applied without adding a control. The complete source instruction
CFG remains identical, and the separate-head macro word is unchanged.

The resulting scanner_best196 table is a third fully checked 196-control
layout, with 69 AX readers and seven compatible folds. It passes all 4,780
contracts (maximum 515, total 1,548,633 symbolic steps), exact blank startup
at 58,294 steps, and all 196 controls are graph-reachable. Its remaining
obstructed source ordinals are 197, 584, 786, 867, 1759 and 2068. These leave
the deletion of scanner state 34 unjustified by this simulation certificate.
The checked 196-state table does not meet the strict 195-state target.

Rebuild and verify that layout from this directory with:

    python3 export_scanner.py scanner_6 scanner_best196

The checker also verifies the exact original relative macro control flow,
free-algebra emitter identity, unchanged register engine, and unchanged
source CFG under the exterior rotation. Tables, full source sites, native
folds and the receipt accompany it. The scanner annealer and its final log
are provided as anneal_scanner.py and anneal_scanner.log.

Two finite local follow-up screens found no improvement from scanner_6:
188 distinct single-occurrence rotations, then 586 seen trees in a bounded
two-move screen (the first move may break a shared subtree). Their code and
logs are retained. These experiments establish no impossibility theorem.

FINAL COMPLETED SCOPE

The main all-helper/free-ii run completed all 160 cycles (256,000 attempted
rotation proposals) in 968.13 seconds and never improved the effective AX
cost below 62. The scanner portfolio completed all 30,000 attempted
proposals in 178.37 seconds and reached six internal scanner obstructions.
The exact completed logs accompany the two source programs.

All 98 saved cost-62 ties are retained in ties/. Additional finite screens
on those 98 grammars plus scanner_6 found no ordinary action-bisimulation
merge and no compatible second folding round after the selected first
round. Their code and logs are bisim_screen and iterative_fold_screen.
The exported exterior-rotated scanner_best196 table also has 196 distinct
action-bisimulation classes. No experiment here establishes a lower bound.

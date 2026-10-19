# Independent grammar/routing search against the pinned 245-state candidate

## Result

No valid machine below 245 working states was found. The best grammars retained 128 rules, giving 245 states with the existing 117-role framework. This is a bounded search result, not a minimality theorem.

Pinned source: VladimirReshetnikov/ProveIt, commit 5b154d85fac5f7190d65bf7134cab374e580c69e, Computability/BusyBeaver/Research/ZFC/candidate-routing245. The canonical starting table SHA-256 is 17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13.

All executed search, parsing and checking programs in this directory were independently authored for this investigation. Downloaded repository Python/C++ files were read as source text only; none were executed, imported or compiled. Mathematical JSON/text/table inputs were parsed as data. No repository files were changed.

## Exact local findings

1. The apparent one-rule saving replaces eijkKCeijkfg → eijk · KCeijkfg with eijkKC · eijkfg, then removes KCeijkfg. It preserves literal expanded words but fails the special entry (218,0): projection00 changes from eijk to eijkKC. Its expanded source zero-run increases 6→7. It is not a valid 244-state candidate. Independent runtime work found concrete failures; those witnesses belong to the separate runtime audit.
2. Keeping all 54 sufficient bootstrap row locks makes a source maximum zero-run of5 impossible. Five locked zero edges force
   eijkKCqkjGeU → eijkKCqkjGe → eijkKCqkjG → eijkKC → eijk → e.
   Atom e then takes a fixed zero edge to dec register 1. This forces six consecutive zeros in source root 172. The exact certificate is zero5-strict-obstruction.json, checked by verify_zero5_obstruction.py. This closes only the all-locks zero5 lane.
3. A finite relaxed-bootstrap neighborhood was exhausted: at most two elementary reassociation rotations of a shared binary grammar rule, with at most one newly synthesized concatenation helper per rotation. All other rules remain unchanged. All combinations of existing route words matching the 22 required projections were considered. The 54 locks and 18 bootstrap-only root requirements were released; the 14 roots entered by unchanged framework transitions remained mandatory. Router-only synthesis is outside this finite neighborhood.
   There were 26,001 raw proposals,13,562 distinct rule maps and 10,191 compatible route assignments. Of these, 2,153 rule maps were orientation/routing compatible and used at most 128 reachable rules. Their minimum rule count was 128 and their minimum source zero-run was 6. Thus no smaller or zero5 candidate exists in this specifically enumerated family. These are abstract grammar checks, not fresh binary runtime certificates.

## Stochastic search frontier

All heuristic runs terminated normally at their stated time caps. Each tested terminal orientations, binary concatenation, route projections, source zero-run≤6 and depth≤64. Every retained ordinary source root had unchanged terminal expansion. Counts are proposals, including rejected/repeated grammars, not distinct candidates.

| Engine / seed | Time cap | Proposals | Accepted | Best rules | Scope |
|---|---:|---:|---:|---:|---|
| Python rotations /123 |120s|976,524|69,825|128|Fixed route words,54 locks,32 roots plus route roots |
| C++ rotations /42 |300s|40,009,951|3,687,467|128|Fixed route words,54 locks,32 roots plus route roots |
| C++ rotations /71 |240s|26,685,054|3,143,732|128|Fixed route words; locks released,32 roots retained |
| Joint routing /729 |300s|12,490,084|3,830,372|128|Dynamic matching routes, synthesized router-only words,54 locks |
| Joint routing /2026 |240s|12,191,170|4,276,499|128|Dynamic routes and router-only synthesis; locks released,32 roots retained |
| Joint routing /647 |180s|9,838,294|3,535,376|128|Dynamic routes and router-only synthesis; locks released; only14 unchanged-framework roots retained |

Total 102,191,077 proposals. Joint searches can choose route words outside source substrings. Saved 128-rule best grammars are search diagnostics, not newly certified machine submissions. Time-based cooling means repeating the same seed/cap on another machine need not yield identical proposal counts or grammar bytes.

## Restricted mixed-integer models

The models encode a finite pool of possible word rules, binary production selection, child closure, fixed route words/projections, terminal orientations, all 54 bootstrap locks, conservative leading-zero bounds, and depth≤64. They also retain the static semantic roots needed by the atom templates. They do not encode arbitrary novel router words or arbitrary single-use substrings.

- Repeated substrings of the main word of length ≤40, plus baseline/original rule words and atoms: 2,286 words,24,402 possible productions,29,218 variables,146,523 constraints. HiGHS reported the ≤127 model infeasible. A separate ≤128 control run returned 128 and its grammar passed the independent structural checker. The infeasibility replay completed in 1.97s. This is floating-point solver-reported evidence in a restricted model, not an independently checked mathematical lower-bound certificate.
- Adding all main-word prefixes and suffixes: 3,661 words,42,155 productions,49,721 variables,253,563 constraints. A 180s run timed out without a feasible ≤127 witness.
- The same expanded pool with at most 12 baseline productions changed: 90s timeout without a feasible ≤127 witness. A timeout is not an infeasibility result.

Logs and JSON records preserve each terminal status. milp-40-bound128-result.json is the control run; milp-40-bound127-result.json is the fresh restricted infeasibility run. Earlier generic filenames should not be interpreted as different mathematical claims.

## Reproduction and inputs

Set B245_INPUTS to a directory containing the input files below. Set B245_OUTPUTS to a writable output directory. In this portable distribution, Python scripts default inputs to the sibling inputs/ directory and outputs to the script directory. The package rebases paths only and adds assertion guards; retained run logs still describe the original investigation. C++ programs take input/output paths as arguments. No package installation is required for stdlib searches; MILP scripts additionally require NumPy and SciPy with its bundled HiGHS. C++ searches require a C++17 compiler.

Required mathematical inputs:
- candidate-routing245/grammar.json
- candidate-routing245/zfc_routing245_old.tm
- inputs__semantic.txt
- inputs__state_reduction__route-constraints.txt
- inputs__state_reduction__bootstrap-lock54.txt
- inputs__closed-sequence-grammar-next22.json, for the exact zero5 obstruction checker
- certificate__allocation.json, for deriving the 14 unchanged-framework roots

Preparation: python prepare_search.py; python prepare_joint.py; python prepare_unlocked_roots.py.

Observed run commands, with executable paths/output prefixes abbreviated:
- python search_grammar.py 120 123
- search_rotations search-input.txt 300 42 rot42.best
- search_rotations_relax search-input.txt 240 71 relax71.best relax
- search_joint joint-input.txt 300 729 joint729.best
- search_joint_fast joint-input.txt 240 2026 joint2026.best relax
- search_joint_fast joint-unlocked-roots-input.txt 180 647 joint647.best relax
- python milp_grammar.py 40 240; independent replay used 40 30
- python milp_grammar128.py 40 30
- python milp_prefix.py 80 180
- python milp_radius.py 80 90
- python surgical_zero5.py
- python verify_zero5_obstruction.py

Each C++ source was compiled with g++ -O3 -std=c++17.

## Remaining escape routes

A stronger search could change more than two grammar associations while relaxing bootstrap, broaden exact grammar candidate pools, or alter source atomization/framework semantics. Any such new literal table would still need exact source bisimulation, universal runtime coverage and a fresh blank-start proof. No finite simulation or search count here establishes behavior of the infinite consistency search.

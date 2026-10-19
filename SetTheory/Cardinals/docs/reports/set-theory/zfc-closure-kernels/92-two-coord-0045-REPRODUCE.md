# Additional grammar-search lane

All files in this directory are research artifacts. No sub-245-state full machine has been established by this lane in the recorded experiments. Root integration should use the completed JSON summary, audit records and selected source files, not interpret a search checkpoint as a machine proof.

## Inputs

The unmodified input package is `baseline245/zfc245-proof-20261018` in the parent workspace. Set `ZFC245_BASE` to the absolute path of the recovered package when placing these artifacts elsewhere. All Python programs resolve their own adjacent research files from `__file__`; none depends on the original workspace path. For the shell examples set `BASE="$ZFC245_BASE"`. The manifest records hashes of the required inherited files, so relocation does not weaken input identity checks. Its inherited algorithm and attribution are in `code/state_reduction/anneal_routes_zero6.cpp` and the package notices. The derivative sources in this directory retain that attribution. The search inputs are:

- `inputs/state_reduction/route-grammar.txt` (14 required source roots);
- `inputs/state_reduction/route-constraints.txt` (11 caller groups, 22 projections, original AST expression);
- `inputs/state_reduction/bootstrap-lock54.txt` when retaining the original initialization trace;
- `k128-resume.txt` (128 explicit grammar rules and 11 chosen caller roots).

A resume file supplies rules and caller roots only. Thus using `lock0.txt` really omits the additional bootstrap-root constraints; the source-root list still comes from the original 14-root input.

## Derivatives

- `anneal_bulk.cpp`: coordinated deletion/reassociation across all immediate callers of a selected grammar rule.
- `anneal_cold.cpp`: the preceding proposals at temperature 0.02--0.17 and an upper excursion of three rules; useful for exploring the 128/129-rule plateau.
- `anneal_context2.cpp`: additionally rewrites the top one or two splits of an existing grammar word to satisfy a caller's routing projection constraints. Prefix/suffix checks reject impossible words before recursion.
- `anneal_semantic_delete.cpp`: local macro-alias substitution within AX; private-state deletion followed by semantic dictionary reparsing of an exposed frontier. Its minimum-additional-node objective is a heuristic because newly shared rules can be counted repeatedly by the parse tree.
- `anneal_hardzero5.cpp`: context and bulk proposals with a hard maximum source zero run of five, initialized from the constructed free-183 grammar.
- `anneal_semantic_zero5.cpp`: semantic deletion and substitution proposals with the same soft zero-run penalty described next.
- `anneal_softzero5.cpp`: context and bulk proposals with a penalty for each expanded AST node whose leading zero chain exceeds five, while keeping maximum zero run at most six. The last argument is the penalty weight.

The `add_*.py` scripts document how the derivatives were generated. For direct use compile the final `.cpp` file; the generated executable need not be committed.

Example, from this directory with `BASE` referring to the recovered package:

```sh
g++ -O3 -std=c++17 anneal_context2.cpp -o anneal_context2
./anneal_context2 "$BASE/inputs/state_reduction/route-grammar.txt" \
  "$BASE/inputs/state_reduction/route-constraints.txt" output.json \
  300 181047 127 lock0.txt k128-resume.txt
```

The soft five-zero search uses a penalty weight after the resume filename:

```sh
g++ -O3 -std=c++17 anneal_softzero5.cpp -o anneal_softzero5
./anneal_softzero5 "$BASE/inputs/state_reduction/route-grammar.txt" \
  "$BASE/inputs/state_reduction/route-constraints.txt" soft.json \
  300 181054 128 lock0.txt zero5-partial-resume.txt 0.15
```

These are wall-time-bounded randomized searches. An identical seed with a different machine speed can finish after a different proposal count.

## Deterministic routing experiment

`exhaust_context.py` and `exhaust_context_expand.py` enumerate the top-level repair plans for the two callers replacing old state177, with respectively zero or one newly concatenated unconstrained child. Their summaries explicitly delimit this finite screen. They found only three or seven complete recipes on the frozen grammar, all with at least128 rules.

`route_ax_seed.py` reconstructs AX as the route for old caller159/0. `repair_router_ax.py` is the inherited finite beam with a relaxed early-stop target (131rules, zero bad nodes). The accepted seed is `route-ax-470-repaired.json`, which has 131 grammar states and 248 working states in its independent local audit. `route-ax131-resume.txt` and `lock-axrouter.txt` initialize the separate annealing basin while preserving its two AX routing projections.

## Independent audit

`*-local-audit.json` and `search-semantic-smoke-audit.json` were produced by the inherited `code/audit_routing_grammar.py`, unchanged apart from rebinding its reporting base path for an output outside the recovered package. Input paths and all checker rules were retained. These are local grammar audits, not full literal-table/frame/blank-start replays.

`grammar_research_notes.tex` supplies a report section including the forced shared-router word and the exact equivalence between global and terminal zero-run bounds for complete binary AST leaf sets. The runtime counts quoted there are independently visible in the root scanner lane's `second_scan_result.json`.

## Conditional five-zero obstruction and repair

`check_routing183_obstruction.py` checks the immutable finite premises of the human proof in `grammar_research_notes.tex`. With the original AX spelling and caller183/read1 routed to `C=VqkjGqkjGVqkjG`, the five-zero objective is impossible regardless of the number of grammar rules: the projection01 requirement forces leading depth at least5 in C, and the fixed source atom P adds another left edge. The required second projection11 also shows why the shared routing-only state cannot be reused unchanged.

`map_zero5_obstruction.py` prints the two residual offenders in `zero5-feasibility-best.json`. `free_route183.py` constructs alternative caller183 roots and reparses the source C with first child V. It produces six plans with137 rules and maximum zero run 5, recorded in `free183-summary.json`; the representative is `free183-k137.json`. This is an abstract grammar with a passing independent local audit. Accounting is254 working states with the ordinary117-state framework or a hypothetical253 with the second scanner contraction. Neither table was built or fully verified.

The final hard-five-zero run uses only the original14 source roots and no bootstrap locks:

```sh
g++ -O3 -std=c++17 anneal_hardzero5.cpp -o anneal_hardzero5
./anneal_hardzero5 "$BASE/inputs/state_reduction/route-grammar.txt" \
  "$BASE/inputs/state_reduction/route-constraints.txt" rerun-hardzero5.json \
  300 181061 128 lock0.txt free183-k137-resume.txt
```

The recorded output is `search-hardzero5-final.json` with its complete log. `search-summary.json` records the final count and seed; all entries marked COMPLETED have final DONE lines. Stopped search counts are separate lower bounds from their progress logs. Proposal counts do not count distinct objects or prove optimality.

## Recheck finite results

Python3 and a C++17 compiler suffice for this lane. No optimizer or network access is needed for the independent finite rechecks:

```sh
export ZFC245_BASE=/absolute/path/to/zfc245-proof-20261018
python check_routing183_obstruction.py
python audit_search_outputs.py
```

The latter rebuilds all6460 source instruction leaves independently, checks their ordered labels against the original AST, verifies the maximum global and terminal zero runs agree, and invokes the unchanged inherited grammar audit. It writes each `*-local-audit.json` and `independent-audits.json`. The new results retain the inherited checker's ordinary117-state framework accounting, even for a five-zero grammar. They do not claim that the additional scanner contraction has been replayed on these candidates.

The supplied finite beam repair programs use explicit paths, for example:

```sh
python repair_zero5_feasible.py search-softzero5-c50.json \
  --inputs "$BASE/reference/grammar" --lock lock0.txt \
  --output rerun-zero5-feasibility.json --depth 8 --beam 40
```

That beam reached135 rules with two six-zero offenders; despite the name, `zero5-feasibility-best.json` is not itself a five-zero grammar. The following explicit caller183 repair is what first achieves five:

```sh
python free_route183.py
```

`MANIFEST.json` contains SHA256 hashes and sizes of the portable research files plus immutable inherited dependency hashes. `SHA256SUMS` checks the selected adjacent files. Executables, Python bytecode and superseded incomplete prototypes are excluded. The final C++ sources can be compiled directly; generator scripts are included as development history and are not required to reproduce a completed run.

The final run completed 6,473,735 proposals in 300 seconds and ended at 135 rules, maximum zero run 5 and depth 52. The local audit passes, giving 252 states with the ordinary framework and only hypothetical 251 after the additional scanner contraction. `hardzero5-k135-resume.txt` records its exact rules and routes for future work. Ten completed runs total 54,653,830 proposals. The raw optimizer checkpoint field `framework_states=118` predates removal of scanner state 74; the independent `short_scan=True` audit recomputes the 117-state framework used throughout these notes.

The superseded `anneal_context.cpp` and `search-context-1018.*` are retained as prototype history, not counted as a completed experiment. Rejected `route-ax-*-audit.json` files document candidate screening; accepted objects are identified by their `*-local-audit.json` and the summary.

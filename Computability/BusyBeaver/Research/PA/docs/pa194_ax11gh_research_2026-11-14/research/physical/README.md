# New compiler/runtime reduction screens

No sub-194 blank-start machine was certified by these experiments. The accompanying main construction supplies the positive 194-state result. These files record fresh, reproducible efforts to cross the 194 boundary and their exact limits.

## Frozen inputs and provenance

The repository comparison is pinned to `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`. `inputs/primary` contains the original PA194 table and complete source, with native table SHA-256 `e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`. The native labels are start74, dispatcher84 and halt254.

`inputs/gh` contains the new PA194AX11GH constructed in the enclosing research:194 working states,3,671 source sites,4,778 source outcomes, and exact57,922-step initialization. Its own construction receipt is retained. This directory is a search/audit supplement, not a second definition of that positive construction.

`vendor/symbolic_runtime.py` is the inherited oracle-based source-contract checker from the primary PA194 packet. Its arithmetic boxes are assumptions unless separately justified from their literal rows. The marker engine and compiler derive from the attributed PA/ZFC research; the original notices and licenses are preserved in `licenses/`.

`action_merge_future.cpp` and `eliminate.cpp` are copied from `PA/docs/pa194C_conpa_2026-11-13_2/search/physical`. The complete scan-interior collector is adapted from `PA/docs/pa_sub194_research_2026-11-13/research/reduction/collect_source_contexts.py`. The new contributions here are the two-row pair-fusion synthesis, the fresh AX11GH application and evidence, the explicit ZFC-relay transfer rejection, and this portable orchestration. The direct register-alias test is independently implemented; earlier packets already investigated the same type of abstraction on other source programs.

## Results

| Experiment | Scope | Result |
|---|---|---|
| Direct alias of any two primary registers | Exact fixed point of0/positive abstraction from site25 and register seed(2,0,...,0) |263,888 abstract states;3,671 reached sites;all36 register pairs have conflicts |
| Merge301 into88 plus one arbitrary encountered helper-row edit | Radius10;80-step local joins;42 windows;772 possible first actions |5,649,890 two-row specifications;18 local survivors |
| Merge16 into122 plus one arbitrary encountered helper-row edit | Radius10;80-step joins;1,081 windows |4,791,766 specifications;0 local survivors |
| Validate the18 first-fold survivors | All4,780 inherited source contracts;blank start74 for200,000 literal steps |7 fail source checking;11 oracle-only passes, all involving changed arithmetic-box actions;0 exact clean seeds;9 certified rays and9 bounded exits |
| Merge two AX11GH controls | Conservative radius6 windows,180-step future joins |0 candidates |
| Eliminate one AX11GH control by changing incoming actions | Same windows and180-step bound |0 candidates |
| Directly transplant the documented ZFC marker-relay recipe into AX11GH | Exact changed rows, source contracts and literal blank trace |Source site2 fails after4 outcomes;117 steps reach a certified outward ray |

The18-survivor validation must be read carefully: an oracle-only pass after altering a box row is not a proof that the new arithmetic operation is correct. The familiar51/0 rewrite has its separate allocated-block marker argument in the earlier runtime193 packet, but its blank startup still fails. No other changed-box survivor is accepted here. A bounded exit is not a proof of divergence.

The AX11GH context collector covers all4,778 source outcomes and the entire57,922-step startup. It records30,818 radius6 windows, including6,242 accelerated unary-scan observations. Every interior position of a symbolic self-loop run is included up to window equivalence. Unknown file prefixes and correlations are overapproximated. The23 arithmetic-box controls retain the broader all-tape abstract-reachability windows computed by the C++ programs; their contexts are never narrowed by the oracle.

## Precise search limits

The pair synthesizer is restricted to pairs whose read-one behavior already agrees. It changes the retained control's read-zero action, identifies all incoming targets of the removed control, and permits one additional changed transition row encountered along the first local test trajectory. Candidate actions range over both write bits, both directions and every retained working control. The old continuation and candidate path must meet at an identical whole-window tape, head and mapped control within80 steps. Exits from the radius10 window and cycles terminate a local attempt. The first-trajectory filter, the chosen pairs and the step/window bounds limit completeness. These are nomination screens; later full checking is mandatory.

The AX11GH common-action merger and per-incoming-edge deletion have their original explicit avoidance conditions for changed-row dependencies. They seek finite local joins with the old future. They do not cover arbitrary multirow rewrites, new register encodings, deeper or longer helpers, a changed source calculus, or new blank initializers. Their zero results are not global lower bounds.

The zero/positive abstraction is sound because increment sets a bit; a positive decrement nondeterministically remains positive or becomes zero; a zero decrement takes only its zero successor. A direct alias is certified only when every access to either member occurs with the other member zero. Every pair conflicts in this overapproximation. A conflict can be spurious, so this does not prove that all semantic aliases are impossible.

## Offline reproduction

Python3.10+ and a C++17 compiler named `g++` suffice; assertions must remain enabled. No network, repository checkout, solver or proof assistant is needed. Use a new output directory:

```sh
python3 -B reproduce.py --work /tmp/pa-runtime-fresh
```

This replays the abstract fixed point, literal relay counterexample, both targeted pair screens, all18 provisional survivors, and both AX11GH local screens using frozen conservative contexts. It checks the observed search counts and results. To regenerate both complete symbolic context files as well:

```sh
python3 -B reproduce.py --derive-contexts --work /tmp/pa-runtime-full-fresh
```

Context regeneration can take a few minutes. It checks byte identity against the recorded context files. All writes are confined to the requested new directory. The scripts and recorded outcomes are executable mathematical evidence, not a new Lean/iPRA endpoint.

See `ZFC_TRANSFER.md` for the source-grounded comparison with the suggested ZFC research. `recorded/relay_transfer.json` contains every state, head and finite tape support before the certified ray, so its rejection can be replayed without trusting the source oracle.

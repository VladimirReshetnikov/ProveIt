# Source search by reordering and renaming AX schemas

This packet contains source-level research. It supplies **no binary machine with fewer than 246 working states**. Source DAG nodes, observed decoder entries, and binary machine states are distinct quantities.

The baseline source has 203 unique binary nodes. A previously delivered ordered reassociation reduces that to 201; `data/sparse201.json` preserves that prior result. The present search found a different 201-node source in which only the Lukasiewicz schema exchanges the roles of `a` and `b`. The remaining seven logical rows keep their parameters and order. GEN and its cache read remain first; the set-theoretic bundle, parameter reads, and final gates remain in their original positions.

## Concrete source result

`focused_milp_results/dictionary_max24_freq2_zero7_depth64_old1.json` is the new source. Its independently checked metrics are:

| Quantity | Value |
|---|---:|
| Unique reachable source nodes | 201 |
| Leading zero depth | 3 |
| Maximum zero run in source leaf addresses | 7 |
| Maximum source leaf depth | 39 |
| Instruction leaves | 6,460 |
| Decrement occurrences | 1,931 |

The schema row is

`((c -> u) -> b) -> ((b -> c) -> (a -> c))`

in place of the corresponding original row with `a` and `b` interchanged. The complete source normal form is checked against this exact changed formula construction. This equality erases only association of closed sequential components; all fixed control atoms retain their meaning.

The initial reuse-oriented parse of this same changed row had 202 source nodes, maximum zero run 8 and depth 37. The finite-dictionary optimization found a 201-node, zero-run-7 incumbent. Its 120-second solve ended at the time limit; it did **not** prove optimality. The model has 4,419 phrases, 74,349 integer variables and 361,818 constraints. The incumbent selects 139 sequence phrases, beside 62 fixed control nodes.

This is a different source presentation at an already attained source count. It establishes neither a smaller binary machine nor a general improvement over the previous 201-node source. No historical-priority claim is made for parameter renaming, grammar optimization, or source reassociation.

## What was checked

Run these standard-library checks from this directory, with assertions enabled:

```sh
python3 verify_candidates.py
python3 check_macro_bridge.py
python3 price_modal.py
```

`verify_candidates.py` independently parses and traverses the old 201-node source, the new preliminary 202-node source, and the new optimized 201-node source. It checks acyclicity, complete reachability, legal operations, the entire source normal form, exact parameter assignments, one occurrence of the `u` read, and the reported counts.

`check_macro_bridge.py` checks all 15 AX helper implementations against the original 219-node helper program. Each helper has an explicit halt continuation. The generated finite test-to-test relation has 292 pairs in total. Every branch is replayed independently after relation generation: tested registers agree, intervening increment multiplicities agree, and successor pairs are present. The ordinary induction argument therefore applies to arbitrary natural register values. These are source-level certificates; they do not involve a binary tape machine.

`price_modal.py` checks a deliberately limited cost diagnostic. Of the new source's 201 nodes, 177 have normal forms matching an old source node; those matches use 168 distinct inherited modal entry labels. There are 24 new node normal forms, giving the static figure 192. This uses the archived decoder-entry observations. It supplies no compiler, no lower bound, and no assurance that any inherited entry remains compatible after the rewrite.

The ordinary theorem that each selected schema permutation preserves the refutation search is a separate logical argument in the accompanying report. The checks here confirm that the emitted source implements the stated choice of formulas. They do not replace that logical argument.

## Bounded searches and their scope

`original203_seed_result.json` additionally retains the earlier 20,000-proposal
checkpoint with the original203 seed (best 203 nodes, zero run 7, depth 34).
It predates switching the seeded driver to the stronger prior201 input. This
is a recorded negative checkpoint, not an additional successful source.

| Search | Proposal iterations | Best observed source count | Record |
|---|---:|---:|---|
| Reuse-oriented parsing, seeded with the prior 201-node source | 100,000 | 201, the prior seed | `results201/summary.json` |
| Dependency-weighted parsing of the same family | 20,000 | 201, the prior seed | `weighted201/summary.json` |
| Collection of changed source words, also allowing a one-read `u`/`b` exchange in the Lukasiewicz schema | 12,000 | 202 for a changed word | `novel_candidates/summary.json` |
| Coordinated finite-dictionary parse of one selected changed word | One 120-second solver run | 201 incumbent | `focused_milp_results/` |

The first two families allow permutations of the eight logical rows and independent permutations of `a,b,c` in each row. GEN and its cache read, the final bundle, and cleanup are fixed. The third family also permits the `u`/`b` exchange only in the four-argument Lukasiewicz row, where each occurs once; its emitter checks that `read_u` and the move from `u` each occur exactly once. It saves 38 selected changed-source controls.

Iterations may repeat choices, produce the unchanged source word, or use different parses of the same word. They are not counts of distinct machines or exhaustive domains. The reuse-oriented search considers existing phrases plus new joins, so coordinated sharing through novel substrings can be missed. The MILP supplies one such coordinated search for one fixed changed word. None of these observations is an impossibility theorem.

Reproduce the three discovery campaigns with:

```sh
python3 seeded_order.py --runs 100000 --seed 246194 --output /tmp/ax-seeded
python3 seeded_weighted.py --runs 20000 --seed 246196 --output /tmp/ax-weighted
python3 collect_novel.py
```

The third command refreshes `novel_candidates/`; use a disposable copy to preserve the delivered evidence. The first two standard-library campaigns took approximately 434 and 128 seconds in the recorded environment. The exact timing is not part of the mathematical claim.

Only the finite-dictionary discovery step needs NumPy and SciPy:

```sh
python3 -m pip install -r requirements-search.txt
python3 focused_milp.py
```

The recorded solve used the imported dictionary optimizer in its original source environment. The portable `milp_dictionary.py` changes only its environment import to `milp_context.py`; the integer model and solver logic are retained. `focused_milp.py` recreates the same specified source word and dictionary. Time-limited solver incumbents can vary between runs. The delivered incumbent is checked without a solver by `verify_candidates.py`.

## Binary compilation remains unresolved

The existing source203 decoder shares physical entries that inspect preceding address bits. The new word and new bracketing may change the meaning of those bits. Retaining an observed entry label does not establish that its complete tape contract survives.

The generic archived physical-grammar emitter assumes the old required entry words and checks bisimulation with the old pointwise register program. A schema-role permutation changes that word and need not preserve pointwise AX output. The sparse archived compiler, in turn, implements only specific reassociations. Neither provides an immediately applicable, verified compiler for this changed source.

A complete machine construction still needs literal transition generation, caller/context compatibility, all unbounded instruction contracts and induction-support rows, an admitted blank startup, and the logical halting transport. No candidate transition table is silently inferred from the source count or static price. Other compiler designs and further sharing remain open.

## Files and provenance

`source_model.py` is self-contained. It reconstructs the full logical prefix in the pinned original203 source before applying any schema changes. The data directory contains the exact original203 source, the attributed prior 201-node reassociation, a parsed original219 helper table, and archived decoder-entry data.

`PROVENANCE.json` names the inspected ProveIt snapshot, the incoming source, upstream pins, derivations and runtime versions. The original 254 construction is attributed to Mira-Cult, the upstream formal verification to Jeff Ketchersid, and the public compiler to Andrew James Wade. The 201-node ordered seed and imported dictionary optimizer are attributed to the previous incoming under246 report. Existing notices are preserved under `licenses/`. No blanket license is asserted for imported source or derived data.

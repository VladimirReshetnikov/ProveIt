# Seven-head, four-gate source search

These are bounded stochastic discovery runs on the separate 190-token AX emitter. They search association, seven head positions, permitted parameter roles, antecedent exchanges, consistent equality orientation, and the diagonal head's parameter choice. The fixed parameter-read prefix stays in place. They do not certify a new physical table or prove a general lower bound.

Every completed family retained best effective reader score 62. With the fixed term 134, that is 196. A score below 62 would require independent simultaneous-fold, emitter, source, full runtime, and startup verification before being called a smaller machine.

## Compile and run

For example, from this directory:

```bash
g++ -O3 -std=c++17 search_four.cpp -o search_four
./search_four 20000000 4483159 rerun_four
```

The three arguments are iteration slots, seed, and output prefix. A run writes compact JSON receipts, progress, and best gate witnesses. Its initial `.hpp` is part of the source and must be next to the `.cpp`. The corresponding JSON input is retained for independent auditing. These inputs are literal data; a checkout or network is not needed.

| Source | Stored prefix | Slots | Seed |
| --- | --- | ---: | ---: |
| `search.cpp` | `head_cpp` | 4,000,000 | 739156 |
| `search_four.cpp` | `four_cpp` | 20,000,000 | 4483159 |
| `search_short.cpp` | `short_cpp` | 10,000,000 | 451655 |
| `search_close3.cpp` | `close3` | 1,000,000 | 777026 |
| `search_close4.cpp` | `close4` | 1,000,000 | 777027 |
| `search_close5.cpp` | `close5` | 1,000,000 | 777028 |
| `search_close6.cpp` | `close6` | 1,000,000 | 777029 |
| `search_close113.cpp` | `close113` | 5,000,000 | 774410 |
| `closeL88.cpp` | `closeL88` | 2,000,000 | 7714422 |
| `closeL103.cpp` | `closeL103` | 2,000,000 | 7714423 |
| `closeL301.cpp` | `closeL301` | 2,000,000 | 7714424 |

Total: 49,000,000 iteration slots and 43,033,542 scoring evaluations. Counts include repeated candidates and initialization work. They are not distinct-machine counts.

`search_short.cpp` incorporates two already identified multi-step bypasses in the fixed engine. The close3--6 runs use zero-register deletion closings after cleanup. The other closing variants use uniform local detours; their proofs are in `../../theory/closing_lemmas.tex`. The source-count/state-count distinction applies to all these runs.

## Independent semantic audit

From the archive root:

```bash
python3 audit/audit_sevenhead_emitter.py --inputs search/seven_heads/inputs_four.json --out /tmp/four_gate_audit.json
```

The independent audit checks the free-algebra emitted formulas and allowed metadata, not the heuristic physical matching implementation. Its negative controls test incorrect metadata and a broken order. Stored receipts are in `audit/`.

## Provenance

The scoring/rotation code is derived from `gate_search/search.cpp` in `docs/incoming/pa_below196_research.zip` at ProveIt commit `906367250a7f96c923147b10df392294bced7be5`. The separate-head baseline grammar comes from `docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip`, member `pa_consistency_research/axioms/separate196/grammar.json`. The changes introduce a seventh independently permutable diagonal head, its parameter choices, four reduced gate spellings, and explicit closing actions. Original notices are retained in `licenses/`.

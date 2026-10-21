# Cache-return AX row-order search

Status: bounded search completed on 2026-10-21. No new 215-state or smaller physical candidate was obtained. This is not a lower bound on row reordering, source encoding, or Turing-machine size.

## Fixed semantics and transport

Baseline: `research215_round4_calculus/cache_stlayout.sites.json`, 201 distinct source nodes and 4709 primitive leaves. Its seven closed, parameter-preserving AX rows are emitted in the order G, rho6, rho5, rho4, rho3, rho2, rho1. The full initial seed, surrounding AX blocks, cache-return MP, and transfer command were retained. The varying row interval is [478,2642), inside the minimal closed cover [158,4577).

Each accepted source has an exact independently checked full ordinal-CFG transport under row permutation. Both continuation-based and address-based edge computations agree. No global unchanged-CFG claim is made for a reordered source. The compiler's row retrieval indices are transported explicitly; see `COMPILER_TRANSPORT.md`. Every result row in the physical receipts records the old stack rows' new indices.

## Completed finite scope

1. All 5040 permutations were covered using existing closed source factors. Each selected cover was associated right, left, and balanced: 15,120 screens. Minimum source size was 201 nodes; 108 combinations (106 unique sources across 36 permutations) attained it. The factor-cover tie rule is finite and deterministic, not globally optimal DAG synthesis.
2. All 106 unique 201-node sources passed the exact row-CFG transport audit and were priced against the validated cache216 donor and its four-history-rewrite context donor. Of 212 trials, 210 rejected decoder prefixes; the two unchanged controls allocated 216 states.
3. The 35 max-zero-seven seeds underwent 6,580 single closed global rotation trials. No 201-node max-zero-six source resulted.
4. A depth-three, width-five closed-rotation beam then examined 72,380 proposals, yielding 123 unique 201-node max-zero-six sources across five row permutations. Their exact CFG transports were checked again. All 246 donor pricing trials completed: 236 rejected decoder prefixes, and 10 produced raw 262-state layouts. No oversized layout is represented as runtime calibrated.
5. One ranked representative of each of those five permutations was tried in the calibrated protected movable-node allocation model, with no new labels. All five were infeasible in that restricted model. Its representable 215-state control was established separately in round four.
6. Two greedy repeated-adjacent-pair association templates were screened for each of the 5040 factor covers: another 10,080 screens, again minimum 201 nodes and no 200-node source. These templates do not exhaust all association trees.

## Reproduction and receipts

- `prepare.py`, `ROW_ORDER_COVER_INPUT.json`, and the owned `ranker` provide the exact extracted factors and permutations.
- `screen_orders.py` / `ROW_ORDER_SCREEN.json` record the 15,120 association screens.
- `audit_and_price.py` / `ROW_ORDER_PRICES.json` record the first 212 allocation trials.
- `repair_zero_runs.py` / `ZERO_RUN_REPAIR.json` and `repair_zero_beam.py` / `ZERO_RUN_BEAM.json` record closed rotations.
- `price_beam_sources.py` / `BEAM_PHYSICAL_PRICES.json` record all 246 repaired-source allocation trials, terminal status COMPLETE.
- `run_protected_shortlist.py` / `PROTECTED_SHORTLIST_RESULTS.json` record the five protected-allocation attempts.
- `screen_pair_compression.py` / `PAIR_COMPRESSION_SCREEN.json` record the additional 10,080 screens.

The useful frontier is the set of 123 explicitly CFG-audited 201-node/max-zero-six alternative sources. The bottleneck in the implemented allocator remains primitive-entry decoder context and label placement, not simply the longest zero run. All executed search/checker code was locally owned; upstream source and transition tables were treated as inert input data.

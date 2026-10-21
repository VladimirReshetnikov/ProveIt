# Corrected-return source / native-allocation family

The finite pricing family is complete. Eighty saved source trees, each with 202 distinct DAG nodes and exactly the intended corrected biased-scheduler control-flow graph, were priced with each of three explicit CC3 entry actions inherited from existing contexts: (1,L,73), (0,L,42), (1,L,138). These actions were provisional at their new contexts, not assumed correct.

There were 240 trials: 201 produced allocations and 39 failed allocator assertions. The lowest raw allocation count was 215, achieved by 24 tables; none reached 214. All 24 raw 215 tables fail their first primitive contract on a concrete valid tape. The first site is CD8 at address 0000, all nine logical registers are zero, the nonempty spare list is [0], and gap is zero. Each returns to the dispatcher in 152 steps with ones in cells 5 through 63, whereas the correct next PC has its sole bit in cell 2. Other expected data cells are unchanged. Thus these are not candidates calibrated by this runtime interface, even though their source CFG is correct.

The separate symbolic checker fails at the same zero guard before proving any case. This is not merely a proof-tool limitation: the explicit finite tape disagreement independently establishes the contract failure. The generic runtime receipt writer was repaired to permit an empty case list and now records the original exception rather than crashing while calculating the minimum duration.

Files:
- REPAIRED_FAMILY_PRICES.json: every allocation trial and count/error.
- first_repair_000.sites.json through first_repair_079.sites.json: exact finite source family.
- SAVED_SOURCE_FAMILY_CFG.json and check_saved_source_family.py: freshly checked exact target-CFG equality for all 80 sources, with source hashes.
- *_entry*.native.tm and corresponding receipts: all 24 raw 215 allocations.
- CONCRETE_REPAIR_PILOTS.json and concrete_repair_pilots.py: concrete counterexamples and owned replay.
- REPAIR_PILOTS.json and check_repair_pilots.py: independent symbolic failures.
- ../research215_round3_calculus/REPAIR030_RUNTIME.json: cleanly recorded sample first-case failure.

The separate bounded source reassociation search completed normally (exit 0) at approximately 16:25 UTC. It considered 23,327 proposals and retained 14,489 distinct valid exact-target-CFG sources over two rounds. There were no sources with 201 or fewer DAG nodes. The best metric was 202 nodes, depth 43, maximum zero run 6. The first round had 288 proposals and 218 distinct valid sources; the second used up to 80 best 202-node first-round sources. Full receipt: REPAIRED_ASSOCIATION_SEARCH.json; elapsed 648.97 seconds.

No claim of global impossibility is made. The enumeration uses set iteration for tie ordering, so a fresh run can choose different equally ranked second-round parents. Exact saved source inputs and hashes, not an implicit deterministic ordering of all ties, define the reproducible 240-trial pricing family. No candidate meeting the requested 214-or-materially-distinct-215 target survived this family.

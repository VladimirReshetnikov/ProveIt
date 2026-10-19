# Grammar and source-rewrite search, 2026-10-18

## Result and scope

This search lane has not produced a validated machine with fewer than 245 working states. It provides a reproducible obstruction to one narrowly specified scanner-shortening route, new search operators, exact source-rewrite seeding, and recorded searches. None of the heuristic failures or numerical mixed-integer results is a proof that a smaller machine does not exist.

The unchanged-source baseline is ProveIt's routing245 candidate, at repository commit `6446ff5668307a2ac6aee1896037f0b792090389`, from `docs/incoming/zfc245-proof-20261018.zip`. The baseline uses 128 transparent sequence states and 117 other working states after the inherited scanner contraction. Finding a 127-rule grammar with the same framework would yield a 244-state candidate; it would still need the independent source, routing, parametric tape-simulation, and logical checks.

The archived `grammar.json` in this search directory is JSON-equivalent to the package baseline but has one extra trailing newline. Its recorded SHA256 therefore differs. The input hashes in the search reports refer to the actual bytes searched.

## Exact obstruction to zero-run five with the original locks

`locked_scanner_obstruction.py` derives the complete source path `1111000000`, ending in the leaf `["dec", 1]`, using only the original semantic atoms, the immutable source AST outside transparent sequences, and the 54 bootstrap projection locks. No mutable grammar rule enters the derivation. The terminal suffix contains six consecutive zero bits, so every grammar preserving those ingredients has maximum source-path zero run at least six.

The path descends from the main semantic root through its locked right projections to atom `J`, crosses two immutable AST edges, then follows the locked left projections through `eijkKCqkjGeU`, `eijkKCqkjGe`, `eijkKCqkjG`, `eijkKC`, and `eijk`, reaching atom `e` and its immutable decrement leaf. The executable witness and input hashes are in `locked_scanner_obstruction.json`.

This excludes attaining the existing sufficient condition “maximum zero run at most five” by reassociating this vocabulary while retaining all 54 locks. It does **not** prove the longer scanner is necessary for every possible tape invariant, and it does not apply after changing the atom boundaries, bootstrap locks, or source program.

`locked_fine_scanner_obstruction.py` extends the derivation to the particular fine-token search family used here: arbitrary transparent dictionary words may cross old macro boundaries, but the 44 available atomic implementations and the 54 exact projection equations stay fixed. The witness enters source sequence roots96 and172 and never enters AX76. It therefore also applies to every AX-only source override explored in this packet. Its separate executable trace is `locked_fine_scanner_obstruction.json`. Changing atomic implementations or bootstrap constraints remains outside this extended obstruction.

Dropping four projections on the first two left-chain words made a zero-run-five grammar attainable in a separate heuristic search, but the resulting grammar had 148 states. It was not promoted to a full machine candidate or a bootstrap-equivalent construction.

## Search operators and unchanged-source experiments

`anneal_compound.cpp` extends the inherited routing-aware annealer with simultaneous node elimination. It chooses a nonmandatory dictionary word, reparses all its direct users by alternative exact splits or one binary rotation, removes that word, and recomputes compatible caller routes. A successful proposal preserves word equality and passes the existing orientation, route, lock, depth, and zero-run checks.

`anneal_fine_compound.cpp` ports that operator to the parent's finer closed-token vocabulary. It additionally retains the parent's moves that change the boundaries of the original semantic atoms. The 44 original atomic implementations remain the available terminals; their keys are variable-length words over 30 finer closed components. A transparent node's key can cross old atom boundaries.

| Experiment | Proposals | Best grammar states | Search source |
|---|---:|---:|---|
| Inherited annealer, seed 245127 | 9,891,070 | 128 | `first-127.json` |
| Inherited annealer, seed 20261018 | 10,136,400 | 128 | `second-127.json` |
| Compound elimination, seed 128127 | 5,405,672 | 128 | `compound-127.json` |
| Four relaxed locks, soft zero-run penalty | 4,409,349 | 129, still zero run six | `zero5-relaxed.json` |
| Four relaxed locks, stronger zero-run penalty | 203,906 | 148, zero run five | `zero5-feasibility.json` |

The first three searches attempted 25,433,142 proposals in total. Proposals are candidate mutations, many rejected before becoming legal grammars; they are not distinct machines or an exhaustive family. Their output JSON files retain the best grammar found, and their logs retain accepted-move, uphill-move, and restart counts. Search durations are wall-clock limits and are not portable performance promises.

## Finite-dictionary mixed-integer model

`solve_dictionary_milp.py` and `solve_fine_dictionary_milp.py` charge one binary variable per active transparent word and one per available binary production. They enforce one selected production per active word, availability of nonterminal children, fixed external roots, atomic orientation restrictions, all 54 bootstrap projections, and joint choices of caller roots and their one- or two-bit projections. The fine version supports an explicitly identified replacement of AX at source state 76.

The model deliberately omits the full zero-run and depth invariants. It is a proposal generator for subsequent independent checks. Each known seed is also encoded as an exact integer assignment and checked against every constructed linear row except the requested smaller state budget. Those controls are recorded under `known_seed_model_checks`.

| Dictionary | Words | Available productions | Requested bound | Numerical outcome |
|---|---:|---:|---:|---|
| Original keys, seed-word union | 177 | 220 | 127 | HiGHS reported infeasible |
| Original keys, repeated-substring expansion | 2,585 | 28,020 | 127 | HiGHS reported infeasible |
| DNE mask32 fine keys, seed-word union | 185 | 239 | 127 | HiGHS reported infeasible |
| DNE mask32 fine keys, repeated-substring expansion | 7,423 | 161,203 | 127 | 120-second time limit; no primal candidate |

These are finite-dictionary numerical results, not independently checked exact infeasibility certificates. The dictionaries omit arbitrary unique connector words. No global grammar lower bound follows. A control run at bound128 found a dictionary solution with maximum zero run eight, independently measured by `grammar_properties.py`; this demonstrates why solver feasibility alone is insufficient for a scanner-constrained machine.

## Source rewrites and exact grammar repair

`seed_dne_variants.py` takes an independently specified revised AX fine-token word and an existing grammar. It aligns the old and new words, preserves unedited binary subtrees, removes deleted intervals, and reparses partially edited regions against the existing dictionary with atomic orientation checks. The `--generic-edit` mode also handles replacements, insertions, and changes of order. It can use a previously overridden source as its starting seed. Every output records the canonical original AX word and the exact new AX word in `source_override`.

The source words are supplied by the theory lane; the seeder does not prove their logical equivalence. All 64 primary DNE seeds passed the independent fine-grammar audit, including all 54 bootstrap locks and maximum zero run six. Mask32 initially required129 grammar states and reached128. Mask63 initially required132 and remained132 in a 360-second search. The two mask32 runs below retain their source metadata and have been independently audited.

| Revised source | Operator | Proposals | Best grammar states | Candidate |
|---|---|---:|---:|---|
| DNE mask32, 1252 AX fine tokens | Standard fine anneal | 6,998,019 | 128 | `dne-seeds/mask32/final_search.json` |
| DNE mask32, 1252 AX fine tokens | Compound fine anneal | 3,093,717 | 128 | `dne-seeds/mask32/final_compound.json` |
| DNE mask63, 1162 AX fine tokens | Standard fine anneal | 6,810,995 | 132 | `dne-seeds/mask63/final_search.json` |

`dne_long_search_summary.json` records candidate hashes and exact audit status. The frozen earlier mask32 snapshot `dne-seeds/mask32/grammar128.json` is a distinct 128-rule grammar with depth49; it was supplied to the parent for full binary verification. The later search outputs have depth51 and are not interchangeable byte-for-byte with that snapshot.

The stronger Boolean target supplied by the theory lane has 1144 fine tokens, using all six double-negation rewrites and one contraposition rewrite. Generic repair produced 143 rules from the original fine128 grammar, or 142 from the final mask63 grammar; both independently passed the fine-grammar audit with maximum zero run six and depth52. A 180-second compound search reduced the latter to133 rules in 2,772,864 proposals. A 120-second standard search reduced the former to135 in 2,605,132 proposals. Both final dictionaries passed the independent fine-grammar audit; `boolean_full_search_summary.json` records their hashes. They do not improve the state bound.

The theory lane then supplied 32 variants around mask32: one unchanged control and 31 single contextual Boolean rewrites. All 32 primary seeds passed the independent fine-grammar audit with maximum zero run six and depth49. The best noncontrol seed is `mask32_local_024`, a contextual exchange of two antecedents, at128 rules. It is a different 1252-token AX source word from mask32 despite the unchanged length. The next initial sizes are130 for local026, and131 for local019 and021. The parent took local024 for a longer search; this lane completed bounded four-second screens of the other 30 noncontrol variants. These screens attempted 2,205,165 proposals, produced no grammar smaller than130 rules, and all 30 final dictionaries passed the fine-grammar audit. `boolean-local-seeds/audits.json` identifies all seeds and `boolean-local-seeds/screen_summary.json` records the completed screens. Directory identifier `1000+i` corresponds to theory record index `i`; it is a file identifier, not a DNE bit mask.

`grammar_lane_ledger.json` records all searches in this lane, totaling 54,532,289 heuristic mutation proposals across the different objectives and source families. The counter includes rejected proposals and revisits. It must not be described as that many distinct checked machines. `grammar_lane_manifest.json` records the selected artifact sizes and SHA256 hashes; it omits the duplicate original and second DNE seeding families and the inherited package snapshot.

## Discovery closure hardening

During the parent's separate 63-mask screen, the original mask49 attempt aborted on a missing reachable dictionary word. That aborted attempt is preserved in the parent records and is not a completed search. The parent retried with a different seed and independently audited the saved133-rule proposal.

`harden_discovery.py` produces `anneal_fine_hardened.cpp` and `anneal_fine_compound_hardened.cpp` without modifying the historical search sources. The changed collector rejects a proposed grammar with a missing reachable rule. It also rejects a caller route whose dictionary word was erased as an atomic key during collection. Initial seed closure failures remain fatal diagnostics. This is discovery error handling; independent grammar and machine checks remain necessary.

A deterministic replay of the original mask49 random seed2026101849 completed125,000 proposals with the hardened standard annealer, recording524 closure rejections and retaining133 grammar states. Its final proposal independently passed the fine-grammar audit. `hardened-mask49.log`, `hardened-mask49.json`, and `hardened-mask49.audit.json` record this check. The 125,000 maintenance proposals are separate from the 54,532,289 proposals in the frozen search ledger above.

## Reproduction

All paths below are relative to this work directory, with the parent's matching `fine_grammar` directory as a sibling. `package` is the unchanged extracted upstream `zfc245-proof-20261018` snapshot. The final repository bundle may rename these directories; pass the corresponding explicit paths.

```sh
python3 locked_scanner_obstruction.py package --output reproduced-obstruction.json

g++ -O3 -std=c++17 anneal_compound.cpp -o anneal_compound
g++ -O3 -std=c++17 anneal_fine_compound.cpp -o anneal_fine_compound

python3 solve_dictionary_milp.py package reproduced-milp127 \
  --seed grammar.json --seed first-127.json --seed second-127.json \
  --repeat-dictionary --max-rules 127 --seconds 120

python3 seed_dne_variants.py ../fine_grammar \
  ../theory_encoding/original_layout_dne_variants.json \
  ../fine_grammar/fine20261018.json reproduced-dne-seeds --mask 32

./anneal_fine_compound \
  dne-seeds/mask32/grammar.txt dne-seeds/mask32/constraints.txt \
  reproduced-mask32-raw.json 240 321270 127 \
  ../fine_grammar/fine-lock54.txt dne-seeds/mask32/resume128.txt
```

The raw C++ search output omits `source_override`, so copy that exact field from the matching seed before invoking the independent fine-grammar audit or source compiler. A changed AX needs the separate logical calibration and the modified-source compiler. Checking finite execution alone cannot certify the required equivalence with consistency.

The new C++ search files derive from the attributed ProveIt routing annealer. Retain the source attribution and upstream licenses in any redistributed bundle.

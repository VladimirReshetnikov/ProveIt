# Source 71 auxiliary replay plan

Source review only. Each command runs in a **new copied package**, with the working directory shown below. The two seed jobs are optional and distinct from the 16 direct checks/family regenerations. No supplied program has been run by this reviewer.

| Job | Working directory | Command | Suggested cap |
|---|---|---|---|
| printed-table | `.` | `python3 -B code/render_table.py --check` | 120 s |
| logical-certificates | `research/formalisms` | `python3 -B formalism_verify.py` | 120 s |
| dirty-seed-control | `research/formalisms` | `python3 -B formalism_dirty_seed.py` | 120 s |
| shared-gate-counterexamples | `research/formalisms` | `python3 -B formalism_shared_gate_counterexample.py` | 120 s |
| equality-fusions | `research/formalisms` | `python3 -B formalism_fusions.py` | 120 s |
| kbp | `research/formalisms` | `python3 -B formalism_kbp_sources.py` | 120 s |
| kbpf | `research/formalisms` | `python3 -B formalism_kbp_sources.py --peirce-f` | 120 s |
| split-bundle-controls | `research/formalisms` | `python3 -B formalism_split_bundle.py` | 300 s |
| grammar-retained-witnesses | `research/grammar` | `python3 -B verify_research.py` | 120 s |
| conjunction-regeneration | `research/grammar` | `python3 -B bundle_permutations.py` | 120 s |
| deeper-dne-regeneration | `research/grammar` | `python3 -B deepen_bundle.py` | 120 s |
| historical-pruning | `research/grammar` | `python3 -B historical_source/check_source_244.py` | 120 s |
| historical-nip | `research/grammar` | `python3 -B historical_source/make_nip_specialization.py` | 120 s |
| joint-equality-dne | `research/joint-source` | `python3 -B generate_combined.py --equality-source reference/converse_source.json --dne-checker reference/check_dne_variants.py --output joint-source-variants.json` | 120 s |
| row-orders | `research/joint-source` | `python3 -B generate_orders.py --dne-checker reference/check_dne_variants.py --output row-order-variants.json` | 120 s |
| rho8-orders | `research/joint-source` | `python3 -B generate_rho8.py --dne-checker reference/check_dne_variants.py --output rho8-variants.json` | 120 s |
| selected-conjunction-seed | `research/grammar` | `python3 -B seed_variants.py fine bundle_variants.json reference/normalized245_grammar.json regenerated_bundle --generic-edit --mask 2002` | 180 s |
| selected-embedding-seed | `research/grammar` | `python3 -B seed_variants.py fine reference/theory_encoding/original_layout_dne_variants.json reference/normalized245_grammar.json regenerated_dne --mask 32` | 180 s |

All caps are unmeasured safety bounds. The JSON records exact entrypoint hashes, outputs, imports and postconditions. Split-bundle imports the included public compiler; its 920-line source needs root read or exact previously reviewed byte reuse. The seed generator catches failures, so inspect `summary.json` rather than accepting exit zero.

Do not invoke the delivery manifest wrappers, heuristic searches, C++ compilers, proof assistants or TeX. Preserve substantive identity assertions. The auxiliary `code/check_whole_frame_candidate.py` indentation defect is separate from the primary `code/check_runtime.py --expanded` path.

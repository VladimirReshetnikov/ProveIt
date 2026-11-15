Logical/source reduction research, 15 November 2026 UTC

No candidate below 194 or at 194 states was found by these searches.
They are additional bounded searches, not a lower bound and not task-success constructions.
The Gamma(H) idea is prior source-level work. H5XD combines the already proved stronger witness head h5X with Gamma(D) diagonal relocation; JH5XD adds the already proved positive first head J.

All search programs use the fixed native engine and tree-DAG association moves, scoring actual simultaneous history-sensitive folds with scanner constraints. The first search also permutes the six ordinary head parameters using the original 190-token block boundaries. H5XD_anneal and JH5XD_anneal preserve their entire emitter words. H5XD_permuted adjusts the boundaries to the 189-token H5X word and additionally permutes each axiom head's independent parameters. Its fixed prefix, diagonal, guarded gate and AX11 tail are outside these parameter permutations.

To rerun a search from this directory:
 g++ -O3 -std=c++17 code/search_combos.cpp -o search_combos
 ./search_combos inputs/H5XD_input.txt inputs/leaf_attrs.txt rerun 240 711156
The JSON ledger provides the corresponding program, input, budget and PRNG seed for every run. The number of proposals at a wall-clock budget depends on the machine; the frozen grammars and complete observed logs are retained.

The nonG_H5XD search restores the older implicit generalization binder d in the H5XD source, while retaining the same stronger witness and relocated diagonal. It is a separate finite grammar experiment; no acceptable 194-state table was produced. Its candidates were priced but were not accepted by a full source proof or literal replay.

To reconstruct and replay the recorded 195-state candidate, run:
 python3 code/rebuild195.py --output /tmp/H5XD195-rebuild
This checks the exact three CopyA-to-CopyD edits against the inherited witness grammar, reconstructs the raw table, applies the eight frozen simultaneous folds, compares all delivered literal and source artifacts, replays the complete startup and all 4786 construction-symbolic contracts. Use --quick only to skip that final symbolic replay. The code/vendor files, inputs/reconstruction195, and licenses make this optional replay self-contained. The finite execution evidence remains separate from the written source-calibration proof.

The candidate195 folder contains a fully reconstructed 195-state H5XD candidate. It is above the user's bound. Its 8 simultaneous local folds, complete source-graph identity, 4786 universal construction-symbolic outcomes and exact 57922-step blank startup passed. The checker uses imported arithmetic-box lemmas; an independent literal replay was not performed because this candidate is above the target. Do not describe it as a smaller result or as a completed Lean theorem.

Attribution: search_plateau.cpp and screen.cpp derive from ProveIt PA/docs/pa194_conpa_2026-11-13/search; search_combos.cpp adapts the search_h5X.cpp in docs/incoming/pa194_witness_research_2026-11-15.zip; search_permuted.cpp additionally adjusts head boundaries and exploration settings. The fixed engine, node grammar and source arithmetic derive from the AX11GDH packet in docs/incoming/pa194_ax11gdh_research_2026-11-15.zip. Original licenses should accompany this subpacket in the enclosing release. Source snapshot is ProveIt d8d4fb10149d6a76a56e615a35648c8c32847cf4.

The audit folder contains a focused review of the inherited revised AX11H written iPRA calibration and an exact logical proof fragment for H5X+Gamma(D) relocation. Its scope is stated in the files.

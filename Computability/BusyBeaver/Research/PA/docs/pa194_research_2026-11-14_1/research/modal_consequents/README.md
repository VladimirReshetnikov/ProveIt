# Generalized modal heads with an independent consequent

This supplementary experiment proves two new axiom presentations equivalent, by primitive-recursive syntactic proof translations, to the calibrated numerical calculus used by the PA194 family. It does **not** present a verified physical machine with 194 or fewer states.

The new first heads are

- BA: `N(H) -> U(D, I(U(D,H),A))`;
- BP: `H -> U(D, I(U(D,N(H)),A))`.

In each schema D, A and H are independent numerical parameters. Both retain the incoming witness packet's H5X schema `U(D,N(E(H,D))) -> A`, the diagonal, distribution, guarded separation, restricted implication basis and all other retained heads. Their 188-token emitters are distinct from the previously delivered positive join J/J_A presentations.

`generalized_modal_heads.tex` gives the complete new argument, its proof-checker basis and the arithmetic uniformity explanation. `certificates/` contains four new frozen universal Hilbert certificates and two inherited witness translations. The independent replay admits only K, S, Peirce, MP, theorem generalization and the explicitly named numerical heads. K/S/Peirce are inherited *derived* rules of the unchanged restricted rho8 schema, not propositional truth-table oracles. The four checked derivations have 180, 204, 220 and 382 rows. Proof-assistant kernel checking is not claimed.

## Fast reproduction

Run from this directory with Python 3.10+ and assertions enabled:

```
python3 reproduce.py
```

This regenerates certificates in an isolated temporary directory, byte-compares every certificate, independently checks all six derivations, regenerates both complete grammar-search input files and byte-compares them, checks the final best grammars' exact emitted formulas, and validates the completed-search log receipts.

## Search reproduction

The search inputs retain the 134-control fixed runtime and make all six ordinary head orders and per-head parameter permutations available. The stochastic moves only reassociate trees, reorder heads or permute the three independent schema parameters; source and physical certification would remain separate obligations for any favorable nomination.

```
c++ -O3 -std=c++17 search_J_full_order.cpp -o /tmp/modal_head_search
/tmp/modal_head_search BAh5X.templates.txt leaf_attrs.txt /tmp/ba-rerun 600 202611152011 > /tmp/ba-rerun.log
/tmp/modal_head_search BPh5X.templates.txt leaf_attrs.txt /tmp/bp-rerun 600 202611152013 > /tmp/bp-rerun.log
```

Each invocation has a 600-second wall-time limit. Machine load changes the number of attempted mutations even with the same PRNG seed. The frozen input files, actual logs, final best grammars and `search_receipt.json` identify the observed runs. State nominations are `134 + effective reader score`; neither a small token word nor a bounded failed search proves a lower bound.

## Observed results

Both 600-second searches finished without a qualifying nomination. BA attempted 3,578,046 mutations (633,431 accepted), obtaining 76 reader nodes with 11 compatible folds. BP attempted 4,088,745 mutations (728,968 accepted), obtaining 75 reader nodes with 10 compatible folds. Both best effective scores were 65, corresponding to a 199-state nomination after adding the fixed 134-control runtime. These are recorded compiler scores, not a certified physical machine or an optimality result.

## Attribution and scope

`hilbert_builder.py` and the initial independent checker are adapted from the incoming `pa194_witness_research_2026-11-15.zip` at ProveIt commit `e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f`. Its compiler fixed rows, JH5X tree, grammar scorer and search engine are retained as explicit frozen inputs. The new contributions here are the BA/BP schemas, their uniform proofs and new certificate generation/replay, independent emitter bindings, and the recorded compilation experiments. `provenance.json` identifies the original source bytes.

The inherited derivation of the restricted propositional basis is in `PA/jamesyc-upstream/pa196/M6/Logic/RestrictedImplication.lean` and `PA/jamesyc-upstream/pa196/PA196/Logic/ImplicationBasis.lean`. This supplement does not independently rebuild those Lean proofs or the complete PA calibration.

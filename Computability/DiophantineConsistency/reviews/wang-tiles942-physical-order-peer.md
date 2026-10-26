# Independent review: exact physical-order data

PASS. I independently read all 1324 data lines, all 180 order-proof lines, all 65 checks lines, and the author receipt. I found no mathematical or source-binding gap. complemented47_review authored this packet and its actual table/permutation prerequisites; I did not author or modify them. My separate kernel, word, and arithmetic-construction modules are not premises of this packet. This review does not claim a new proof or full fresh replay of the decimal machine's transitive closure.

## Frozen bindings

| File under `Lean/DiophantineConsistency/` | Lines / bytes | SHA256 |
| --- | ---: | --- |
| `WangTiles942PhysicalData.lean` | 1324 / 31026 | `38a11d1ef8d3391074d4cd347e0f764417c6502afd9a6a064d54266456396f5b` |
| `WangTiles942PhysicalOrder.lean` | 180 / 6945 | `eafbd5914bf4219d6ce48b501c8be41c228253ef719b65a02e7d167ada0ce3e9` |
| `WangTiles942PhysicalOrderChecks.lean` | 65 / 2816 | `9d7bfcf65995b05546b19c89d44b9de8bb1bdb1bc3e41cf8c9a6060dd7e43460` |

The reviewed author receipt is `reviews/wang-tiles942-physical-order-author.md`, SHA256 `92f114144e778add32e6e02ae962ae0dbb593fb6fcf26a7108ebb6be0c97ab99`. I also read the complete actual `WangTiles942Permutation` and `WangTiles942Core`, the relevant exact decimal decoder/action-cache/target/rail definitions and binding theorems, and the pinned adjacent-order helper interfaces. The imports bind `tile` to the actual decoded table, and `physicalPosition` to the full printed floor formula.

## Mathematical review

The literal data consists of 58 blocks of 16 pairs and one of 13. Every pair is checked in Lean against the actual selector weight and a positive abstract index below 942. `rows_good` composes all 59 proofs; it does not assume the data generator was correct. `rows_descending` separately checks every adjacent strict inequality, including block boundaries.

`value_strictAnti` derives full strict order from those adjacent comparisons. Equal abstract indices would have equal actual weights, so the non-Start index map is injective. Finite injectivity gives complete coverage. This does not import a permutation claim from JSON or rely only on spot checks.

The rank proof has the correct direction: decreasing weights give increasing strict-upper-set ranks. The resulting `rankMap` is a strictly increasing self-map of `Fin 941`, so the generic finite-order theorem makes it the identity. I checked its finite-surjectivity/strong-induction argument, including its vacuous `Fin 0` case and singleton case. Combining this identity with the existing printed-floor theorem proves every listed position without evaluating quadratic floor comparisons in Lean.

Start is handled separately at physical position zero. The full `abstractAt` has both inverse identities with the actual `physicalMap`, is bijective, and equals the existing `physicalEquiv.symm`. The weight binding and arbitrary-additive-commutative-monoid `selector_sum_reindex` therefore reindex the actual complete selector sum, preserving all weights and positions. No injectivity, coverage, floor-rank equality, or missing-tile calibration is supplied as an unproved hypothesis.

The focused checks preserve the initializer at position 504, the final weight 1025, and the distinction between protected Start and the descending non-Start list. In particular, Start's weight is below the first non-Start weight; silently sorting it into that list would be wrong.

## Independent complete reconstruction

I wrote, read, and ran a separate standard-library-only reconstruction in `/tmp/wang-physical-order-controller-peer/recompute.py` (SHA256 `527d89f78b528af673846923c1e3207e8f3696e7c97fcfb1c957c1f23a6a7162`). It imports no project code and executes no incoming generator. It reads the complete 715-digit numeral from the actual Lean decoder source, independently performs all mixed-radix/signed-target decoding, reconstructs the 45/199 target sets and rails, and builds all printed tile families.

It matched all 430 cached actions, all 942 distinct tiles, every one of the 941 non-Start literal pairs, all 940 adjacent inequalities, and all 885481 literal floor comparisons. It independently recovered initializer position 504 and final pair `(433,1025)`. Wrong-coefficient and swapped-adjacent-pair diagnostics were rejected; these are computational diagnostics, not additional Lean theorems. The numerical reconstruction is supporting evidence, not a trusted formal premise.

The deterministic reconstruction receipt `/tmp/wang-physical-order-controller-peer/recompute.json` has SHA256 `51369a9b2f4e7ee9a36e40b65543e2a94ec1019396e06d5aceb8992c79162cfc`. Its hashes of complete reconstructed arrays are:

- Actions: `4c81320292708dae99501de44503470418fc7ae8703e4b95d01117be2961016c`.
- Tiles in abstract order: `3fda0b730eb2698fe3bb399100843fcf9223631607b49f138793e0b157371067`.
- Non-Start physical pairs: `362de053598c3bfa3facee341a6b2fc46a66eda74ecf98904a33c7dd3c9209a8`.
- All physical positions in abstract order: `1b59692fdc532fffd605d9569a47f8173adc5308a2ba993074eaef437b30c517`.

## Isolated fresh replay

After reading the sources, I created `/tmp/wang-physical-order-controller-peer` with the three reviewed module stems absent. Other required project objects were symlinked unchanged, and the overlay was prepended to the existing Lean path. Data, order, and checks were compiled sequentially there with Lean 4.32.0, `-M6000 -j1`, and their source-level `Elab.async false`. Thus Order imported the freshly replayed Data, and Checks imported the freshly replayed Order. Shared source and prerequisite object files were not overwritten.

| Replay | Result | Seconds | Peak KB |
| --- | --- | ---: | ---: |
| Data | PASS, no Lean diagnostics | 79.76 | 3550508 |
| Order | PASS, no Lean diagnostics | 5.07 | 3202596 |
| Checks | PASS, sixteen standard-only axiom reports | 11.57 | 3424220 |

All printed axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`; `rows_descending` reports no axioms. No warnings, `sorry`, added axioms, or external evaluation oracle were used by these new files. The three fresh objects are byte-identical to the frozen author objects:

- Data: `485603440813aecddc825140e05022a3730ac65743793a3275e3a16f5470280b`.
- Order: `15f4a92d173c38812990e501e1d46e7efddfd99b0e0a40d024e15d4a8010a77f`.
- Checks: `3df7994d8c1a804c08c361f9b96bd67ab2953c602b0708681cd0b47af616570b`.

The 20 selected source/object/toolchain/receipt inputs were hashed before and after and remained unchanged. The before manifest hash is `3710af0c13c0c5de493e664859b682b8fd3892a0299ef79d2121412c976be58e`. Replay logs, including timing, have SHA256 `e098785e70c6f7f5e4a293b47e9b4b3a5fd435079d6f265f58c306c4489a3b39` (Data), `e0b1e5eb4927f934f051ec2c068bd557e5148e0119debd1794cda2286b5f8430` (Order), and `86891bc236376950039afb149792962eef6b038c65e8fd3eb7f97e71655e0280` (Checks).

This packet proves the exact reusable physical-order binding. It does not itself prove actual K residues, unit or lifting conditions, controller existence, or the remaining equation converse. No source changes are requested.

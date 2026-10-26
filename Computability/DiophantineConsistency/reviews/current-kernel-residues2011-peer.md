# Independent review: actual current kernel residues

PASS. I independently read the full 843-line main, 63-line checks, and author receipt, then freshly replayed both modules in isolation. No mathematical or binding correction is requested. complemented47_review authored this packet and its physical-order data/proofs. I authored the earlier `CurrentKernel2011` prerequisite; this review independently checks the new modular evaluation and its composition with that frozen kernel, not my own authorship of the kernel. No frozen source or shared object was edited.

## Exact bindings

| File under `Lean/DiophantineConsistency/` | Lines / bytes | SHA256 |
| --- | ---: | --- |
| `CurrentKernelResidues2011.lean` | 843 / 32387 | `6e6812f7181a4b7fa5c558aef5f369c3068c21870710d522a979c39c877c8f4f` |
| `CurrentKernelResidues2011Checks.lean` | 63 / 2401 | `e91e763e095b1876b3c09b5ab1043ee69d03eed0b714ff180166d14ccbcea0ba` |

The reviewed author receipt `reviews/current-kernel-residues2011-author.md` has SHA256 `e518bcadda664bba62c2c7bab3c3ee85aa18c6d2f93b269cce888c46366b95a0`. Direct imports are the previously reviewed exact `WangTiles942PhysicalOrder` and `CurrentControllerData2011`. I read the complete latter source, the actual kernel definitions and whole-word identities, and checked the physical reindex interface against my completed physical-order peer review. The controller data's formerly explicit K premises are discharged here by new unconditional theorems about the same original K.

## Mathematical review

The generic evaluation and append proofs are valid in any commutative semiring; no field division, primality, or unproved modular inverse is used in the main evaluation. `evaluate_sum` has the correct high-to-low exponent `length-1-j`. The exact proved physical reindexing reserves Start at position zero and places the remaining selectors at positions 1 through 941. Therefore the Start term has exponent 1005 and the 941-entry evaluation receives the multiplier `r^64`: `(940-j)+64=1005-(j+1)`. No selector is omitted or double-counted.

`controlReflection` retains all 34 actual controls in the true packed orientation: west positions 978..985 with shifts 10..17, north 960..968 with shifts 18..26, east 969..976 with shifts 27..34, and south 942..950 with shifts 35..43. Every reflected coefficient is doubled. The three bare powers 18, 1004, and 2020 occur once each. In particular, the reflected contribution sharing exponent 1004 with a bare term is added rather than replaced. The semiring `rawWord_cast` binds this complete expression directly to `CurrentKernel2011.rawWord`.

All 177 short block statements were read: 59 chunks at each of the three moduli. Their proofs kernel-check the actual literal data. Generic append identities assemble the complete 941-entry evaluations; no assumed list residue or generator output is a premise. The protected Start weight and three actual radix residues are checked separately. The cast-to-remainder helper is valid under the stated positive modulus and bounded representative, and the explicit auxiliary-modulus conversion preserves the same K. Local irreducibility avoids expanding the enormous constant during wrapper checking; it introduces no hypothesis or axiom.

The resulting unconditional values are:

| Modulus | radix | Non-Start evaluation | Controls | K | B | H=1+B*K+B² |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 47 | 2 | 15 | 4 | 26 | 37 | 29 |
| 2011 | 1283 | 1822 | 241 | 1995 | 1283 | 674 |
| 120199 | 4237 | 64708 | 88241 | 114787 | 37435 | 36379 |

The checks test the original K without residue assumptions, empty and composite-modulus evaluation, nonzero H, omitted Start, a one-field bare-marker shift, and reflected scale one instead of two. The scale mutation uses the explicitly checked inverse 24 modulo 47; its expression is exactly bare plus half the reflected contribution.

## Independent numerical reconstruction

I authored and read `/tmp/current-kernel-residues2011-controller-peer/recompute.py` before running it. It uses only the Python standard library, reads frozen Lean numeral data, and executes no project or incoming generator. It checks all 177 block residues, all 941 non-Start pairs and coverage/order, and reconstructs the complete finite kernel from 942 selector terms, 34 controls, and three bare terms. The physical data had already passed my separate full seed-to-table/rank reconstruction; that earlier fact is not a new decoder replay in this receipt.

Three evaluation shapes agreed at each modulus: the complete integer K reduced afterward, direct modular summation of all 979 terms, and the reindexed Horner-plus-controls expression. The whole integer has 94941 bits / 11868 bytes, with big-endian SHA256 `64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`. All three mutation diagnostics were rejected. This numerical work is supporting evidence, not a Lean premise.

The script SHA256 is `efb1ee7584ac4f0965e8677b1e36ea92236ccf59d96498a4d56af79d71d37e36`; its deterministic receipt `/tmp/current-kernel-residues2011-controller-peer/recompute.json` has SHA256 `5718b1b020cb75276bd46b9ea14989367974e3a2d8035b15fe2da4a0861b8363`.

## Fresh isolated replay

Both reviewed stems were excluded from `/tmp/current-kernel-residues2011-controller-peer` before compilation. Other required project objects were symlinked unchanged and the temporary directory prepended to the existing Lean path. Main was freshly compiled first; Checks then imported that fresh object. Commands were sequential, Lean 4.32.0, `-M6000 -j1`, with source-level `Elab.async false`. No prerequisite closure was rebuilt or claimed as freshly replayed.

- Main: PASS, 12.39 seconds, peak 3476876 KB, no Lean diagnostics.
- Checks: PASS, 2.93 seconds, peak 3240484 KB, no warnings; all 13 axiom reports are limited to `propext`, `Classical.choice`, and `Quot.sound` or the applicable subset.

Both fresh objects are byte-identical to the frozen originals: main `91a5c3514338ebe9f0ddbd3069e3928ff61595c332017ba773232b8c2a33063e`, checks `db00c44dcd428b7cad190a5dc309c352c9cec681bdf680c258efa92027e79d56`. All 20 selected source/object/toolchain/receipt inputs remained unchanged. The before manifest SHA256 is `c3a976567537ac2e1b401897b6f33d8728a3f57fe13247cd372e643a21def083`. Replay logs including timing have SHA256 `4e591ce7fa95e33b90f98983e57cbf80ea8bdacde9279fad9c076e14d29baa29` (main) and `58373865a385196045ceec1371e974f4d9be59c6cc933eea75c2356aa9ca4c1d` (checks).

This packet establishes the stated finite actual-K and H residues. It does not itself establish LTE, a full power orbit, CRT selection, safe dummy realization, controller existence, a positive polynomial witness, or the final equivalence. No source changes are requested.

# Independent review of the 476-operation U21 source

**PASS on the corrected frozen release.** The emitted source computes exactly the pinned 504 parent's polynomial on identical supplied coordinates. The full count is **476 = 176M + 300A**, with **67 positive witnesses**, two fixed program parameters and ordinary positive input. No further correction is requested.

## Frozen author and read scope

| Artifact | SHA-256 |
|---|---|
| residue_affine_sparse_shared476.py | `52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf` |
| residue_affine_sparse_shared476.json | `90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8` |
| residue_affine_sparse_shared476.md | `cbd4d632b813f0ad34a9e5b35894d187ca229c14f1d4cf3af269a518ab57fcd4` |

I read the complete new helper and proof, and the complete pinned 504 and factored-parent proofs. All seven author dependency hashes were authenticated. The fresh independent checker reads inert JSON/text and never imports or executes a predecessor. The corrected new author helper was separately replayed normally and with `-O` from `/`; both exact replays passed.

The initial author audit mutated a shared parent-row list during its range rewrite. The reviewed release instead creates a fresh row, checks the parent array remains unchanged, and binds the receipt to the helper bytes. My independent reconstruction also creates fresh edited rows and checks parent immutability before and after its whole-source identity proof. Its comparison starts from the untouched, authenticated 504 JSON array. The emitted child polynomial was unchanged by this validation repair.

The inherited native and U21 compiler theorems remain dependencies, not newly recertified historical results. The new semantic claim follows from an identity on all supplied values, so it introduces no new chronology, positivity or decoding obligation.

## Independent reconstruction and identities

The checker reconstructs all 476 row definitions from the authenticated 504 array using its own edit map. It verifies the complete source against that map, topological order, unique producers, all-row/all-port liveness and all 70 free ports. It confirms 38 removed names and ten new names. No undocumented retained instruction changes are accepted.

The population proof expands each of the ten reused registers in the 36 actual raw edge variables. Their supports are disjoint and cover every edge exactly once. Both complete population expressions expand to the sum of all 36 edge hats minus 36. The loader pair and the other class/state sums remain paid and live; their raw-selector dependencies can be scheduled before the new J without a cycle. The 34 replaced population-chain additions become nine additions, saving 25A.

The second proof independently expands both range-repeat expressions in the actual paid `scale_89`; each is `1+P+P^2`. The obsolete multiplication and addition have no remaining consumer after the range operand is replaced. This saves 1M+1A without introducing a free power or repunit.

For the payload, expansion at the actual quotient, remainder, weighted-word and action-selector cuts proves

    (W+J)+V-S-(J-I-D-T) = W+V-S+I+D+T.

The paid positive quotient U=W+J remains available to its other consumers. The new payload needs five additions/subtractions where the old private zero-action and payload cones needed six. The values of `common_quotient_152` and `common_remainder_153` change, but `common_payload_154` and both final payloads recover exactly their original values.

For the complete identity, the independent checker interprets both entire DAGs, representing each authorized local cut by its proved sparse polynomial in the actual reached boundary expressions. It then checks all 464 same-value retained registers and the full output. It explicitly verifies that the two excluded intermediate values differ; their effects do not escape the restored payload cut. All 72 native-prefixed rows have identical definitions and values. All 20 finalizer rows are retained literally, including the six ordinary residuals, the eight-unit product consumer and final subtraction.

Thus F476=F504 over every commutative ring. Every positive integer zero tuple is preserved in both directions, with no fresh native witnesses, changed supplied coordinates or extra condition. The default coupled/shared parent is the sole emitted successor; un-emitted alternate schedules receive no new claim.

## Interface, count and degree scope

The parameter list remains `program,radix_program,input`; the first two remain fixed program parameters. The valid universal recipe stays E=3^e with fixed dyadic C>=64 and C>E, independently of the varying positive input. The remaining 67 supplied ports are exactly the parent's witness list.

| Part | M | A | Total |
|---|---:|---:|---:|
| Certificate | 169 | 287 | 456 |
| Literal finalizer | 7 | 13 | 20 |
| Full polynomial | 176 | 300 | 476 |

The seven-comparison metadata uses the parent's convention: six ordinary residual comparisons plus the native product condition. The total saving is 1M+27A, exactly 28 operations. The inherited uniform degree bound 5160 transfers by full polynomial equality, including the parent's convention that the program parameters participate in that uniform degree count. No new exact degree, minimum, or improvement to universal 84 is asserted.

## Fresh evidence and replay

The independent receipt records the edit inventory, partition, exact population/range/payload coefficients, whole-DAG identity, immutable parent-array digest and child-array digest. It authenticates both the author's helper-byte binding and its emitted-array binding. Eight additional signed full-source modular comparisons over two primes pass. These are off-zero algebra checks, not accepting histories or positive native Pell tuples.

Fresh normal and optimized exact replays of the independent checker from `/` also pass, using the installed author trio and the portable default author path.

Independent helper SHA-256: `c159901d31df2d41cb08a642d6ef30ca8023212ef30c0730a95ccbfb733bc340`.
Independent receipt SHA-256: `6374343026823f8df560f68ff9b643a5b0b58c9be5b84bdf376cb5279702da94`.

The checker requires `--root ABS_WIP` and either `--output NEW_PATH` or `--expect RECEIPT_PATH`. If the author trio is staged elsewhere, add `--author-root ABS_DIRECTORY`; otherwise it defaults to `--root`. No repository or frozen predecessor was changed during this review.

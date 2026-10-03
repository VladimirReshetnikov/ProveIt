# Independent weighted transport-shear census

The exhaustive weighted objectives for all thirteen first-root bases and their thirteen gap-root counterparts produce **no new Pareto pair** beyond the reviewed 39 saved-source catalogue. The predicted frontier is

    86/178,87/134,88/122,89/112,90/108,91/102,92/80,
    93/72,94/62,95/54,96/50,97/48,98/44.

This closes the earlier *metadata-only* uncertainty within the declared 26-base partition/finalizer grammar. It is an independent arithmetic census, not an emitted-source audit, a new universal upper-bound witness, or a lower bound outside that grammar.

The [checker](transport_shear_weighted_census_independent.py) authenticates seven parent source/proof/receipt files. It executes no author Python or historical verifier. It reads the actual asymmetric parent JSON and the four appropriate linear/gap direct-source arrays, independently walks the ancestors of the required norm ports and retained comparisons, and recounts the gap-root core's multiplications and additions. The actual six-gate gap norm and private gap-coordinate consumers are checked. The proved first-root replacement changes its first weight from 12 to 22 and saves one core addition; transport weight is changed from 3 to 2 without changing the core cost. All eight first-root base kinds represented by previously emitted frontier packets independently agree with their stored exact core ledgers and factor/residual metadata.

For `n` factors, `g` groups, `m` retained ordinary comparisons, and a core of `Mc` multiplications and `Ac` additions/subtractions, the literal group products use `n-g` multiplications. An SOS finalizer adds `m+g` subtractions, the same number of squares, and `m+g-1` additions. A nonempty anchored finalizer has one fewer squared residual but also pays its final multiplication and two final additions/subtractions. Thus both general cases have

    M=Mc+n+m,
    A=Ac+2m+2g-1,
    total=Mc+Ac+n+3m+2g-1.

The sole exception is one anchored group with no retained comparison: its product-minus-one finalizer has `M=Mc+n-1`, `A=Ac+1`, and total `Mc+Ac+n`. The checker counts these instruction classes separately and verifies the compact formula for every objective.

With positive factor weights `d_i`, group sums `s_j`, and maximum retained residual degree `r`, the objectives are

    SOS:     2*max(r,s_1,...,s_g),
    anchor a: s_a+2*max(r,{s_j:j!=a}).

These are the previously proved within-base objectives. The new quadratic transport factor has nonzero leader; no other factor degree changes. The checker does not use raw gate-propagation degrees as exact degrees.

Partition enumeration is independent of the parent's restricted-growth traversal. It recursively chooses the entire block containing the least remaining element, then partitions the complement. Per-base counts are checked against the Stirling recurrence. Each thirteen-base family has six eight-factor, five seven-factor, and two six-factor bases. Therefore it contains

    6*4140 + 5*877 + 2*203 = 29631 partitions,
    6*21147 + 5*4140 + 2*877 = 149336 SOS/anchor choices.

Across both coordinate families this is **59,262 partitions and 298,672 objectives**. The independent enumerator also counts ties at every cost.

A second method cross-checks every per-cost minimum in every base: a subset dynamic program minimizes the maximal unanchored block weight; an independent scan over the distinguished subset supplies the anchored objective. All 26 comparisons pass. This method does not depend on the enumeration's traversal order or selected tie representative.

The result has 202 best-by-cost records. Their predicted literal costs sum to **19,375 operations = 9,702M + 9,673A**. These are arithmetic predictions, not a claim that this checker emitted or proved all 202 full circuits. Root's separate source construction is responsible for connecting its chosen representatives to complete circuits. Different tied partitions or traversal digests are harmless provided the complete cost/degree minima agree.

The JSON records every base vector, its actual gap-core source hash, core count, all per-cost winner plans and tie counts, both-method checks, and the predicted frontier. Fresh exact receipt replay is available from any working directory:

    python3 transport_shear_weighted_census_independent.py --root WIP --expect transport_shear_weighted_census_independent.json

No source or repository file was modified, no native Pell witness was constructed, and the old 149,336-choice verifier was not run. This is a fresh independent weighted enumeration in the explicitly requested finite grammar.

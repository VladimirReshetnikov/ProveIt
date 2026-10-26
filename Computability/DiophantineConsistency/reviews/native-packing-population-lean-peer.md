# Native packing population: independent Lean review

Verdict: PASS for the exact generic statements in the frozen packet. The
proof derives the packed population from actual mask disjointness and strict
block bounds. It does not assume a Pell population lower bound, a calibrated
rank, or any current coefficient tuple.

## Reviewed scope and bindings

The reviewer read the entire 57-line main and 32-line checks before execution,
the entire direct import `NativeMaskPopulation`, and the reused binary
population and carry identities in `Paper1982/Carries.lean` and
`Paper1984/Identities.lean`. The main and checks were authored by the root
agent. This reviewer authored earlier constructed-word, copy, padding, and
rank-variation packets; none is a premise of this generic proof.

Paths below are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/NativePackingPopulation.lean` | `bc4526d0e9f267df6d027b6f7ec38e5374ecc4f1627d556f4cffd41b0f1cd3ac` |
| `Lean/DiophantineConsistency/NativePackingPopulationChecks.lean` | `731d76f53e21c2ac58117ac0bf2eb8a1c77b1d26cfe5bb643d3433ad90a278d3` |
| Direct import `NativeMaskPopulation.lean` | `a98b8175934f6c766933bfdc44d380b349f5b4ba27cf4a46582b0a0352431fc7` |
| Reused `NativeMaskPopulation.olean` | `9283ba8ae42982c3b5debe27ec8b6600ce1210e286448d63537ee9a7a9006d8f` |

## Mathematical audit

`disjoint_add_lt` first replaces the ordinary sum by binary OR using
`A &&& M = 0`. Both individual bounds below `2^u` then bound their OR below
the same power. It does not infer a strict sum bound from two strict operand
bounds alone.

`four_block_exact` rewrites the expression as nested radix blocks and applies
the exact binary split lemma three times. The three lower blocks are strict;
the uppermost block `D` is unrestricted, which is both sufficient and correctly
tested at `u=0`. There is no unproved assumption about carries across blocks.

`mask_population` supplies those lower strict bounds from both actual mask
equalities. The complement `2^u-1-A` is strictly below the radix because it is
a natural subtraction from `2^u-1`. The exact complement-population identities
use the explicit `A,F < 2^u` hypotheses, so truncated subtraction does not
invalidate them. Additive population identities and zero carry counts from
both masks cancel the populations of `A` and `F`, yielding exactly

```
sigma(packed) = 2*u + sigma(M) + sigma(H).
```

`calibrated_population` adds only the explicit combined mask-population
identity `sigma(M)+sigma(H)=u+2` and obtains `3*u+2`. The desired population of
the packed integer is never an input. This direction is independent of the
older saturation theorem's Pell-derived lower-bound premise.

No particular repeated-mask origin adjustment, current rank polynomial,
strictness of current scalar words, or consistency equivalence is established
by this generic module. Those remain separate application obligations.

## Fresh isolated replay

The two frozen files were replayed sequentially under the pinned workspace
environment using `lake env`, `lean -M6000 -j1`, and their explicit
`Elab.async false`. A fresh overlay excluded both target objects and placed
their newly compiled replacements before existing dependencies on `LEAN_PATH`.
Thus checks consumed the fresh main object; no existing source or object was
overwritten. Existing prerequisites were reused, not freshly replayed.

The serializable command, source-preservation, log, and object receipt is:

`/tmp/native-packing-population-peer-yfhkujtu/REPLAY.json`

SHA-256: `e23f65946477c86ef10ce469e82a710290f9fe588da0b7e00de2dd63c6fa3d35`.

| Build | Result | Time | Peak RSS (KiB) | Fresh object SHA-256 |
| --- | --- | ---: | ---: | --- |
| Main | PASS, no diagnostics | 3.29 s | 3,201,780 | `d341915f63fc947decd8e0e9031cad64618cf02a5b4a4cff4aee1ff0c5409f48` |
| Checks | PASS | 2.96 s | 3,191,564 | `ca9b8ef4ce09c90b7537192fd7a7ae37e302a74335cc83f001ed7651d90531b7` |

Both fresh objects are byte-identical to the author's frozen objects. Both
source hashes remained unchanged. Main log SHA-256 is
`a6b218b24ccb29266d993fe9b77153f8b991e658a2ba3c09297701dfb705d2c3`;
checks log SHA-256 is
`95f881323176384d9e408a1b1894dd293fae15d50842ddb15a1de808389ad642`.
All four axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorry`, added axiom, or `native_decide`.

The focused checks retain a zero-width window with arbitrary upper block,
nonzero disjoint sums, a failed population formula when a lower mask overlaps,
and a failure of strictness when two bounded operands are added without
disjointness. Separately, a stdlib Python integer calculation enumerated every
disjoint operand pair in each window `u=0,...,5` and compared the full packed
integer's `bit_count()` to the formula: all 66,430 cases passed. This finite
sanity check supplements, and does not replace, the generic Lean proof.

No source corrections were requested. No frozen source, shared object,
maintained equation, or git state was changed by this review.

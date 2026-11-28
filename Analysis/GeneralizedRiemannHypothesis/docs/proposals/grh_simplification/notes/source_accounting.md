# Conservative audit of the legacy exact-modulus interface

Target: ProveIt `9050b04000647d588d0c78d945180abcd3b0bcf7`.

This audit counts a deliberately narrow set of declarations whose role is the old exact-modulus/aggregate-ratio representation. It excludes all mixed-Gram, boundary, determinant, local L-value conversion, conductor conversion, tameness, and generic counting arguments. The counted old API must still be replaced by the new scalar-budget API; the numbers are **gross candidates, not net savings**.

| Source under `src/New/Determinant/` | Selected declarations | Physical declaration/body lines | With attached documentation |
|---|---:|---:|---:|
| `Chain/Moduli.lean` | 18 | 87 | 120 |
| `Chain/NormOfChain.lean` | 5 | 33 | 52 |
| `AuxiliaryForms/Turns.lean` | 3 | 8 | 13 |
| `Twist/LongForms.lean` | 1 | 8 | 13 |
| **Total** | **27** | **136** | **198** |

There are 134 nonblank, noncomment source lines within the selected declaration/body spans. Exact declaration names and inclusive line ranges are in `../evidence/metadata_only_audit.tsv`; `../scripts/metadata_audit.py` reproduces them from the pinned checkout. Physical spans include comments internal to proofs; attached-documentation spans additionally include each declaration's immediately preceding documentation.

The 306-line `NormOfChain.lean:142–447` candidate block is a different, larger figure. It includes five of the declarations above and substantial adapters whose mathematical content must be ported. Its 306 lines must not be added to this table without removing overlaps, and must not be claimed as deletable without replacement.

The remaining adapter work is unmeasured. In particular, `CriticalPair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd`, the conductor-power lemma, `HasSmallRatios.heightLe_inv_rpow_mul_prod`, mixed-Gram induction, physical normalization, single-lift determinant transfer and final volume-ratio proof need replacements. All precise square, Fourier, period-transfer, integrality and spanning arguments survive.

A smaller public interface and removal of global exact aggregate products are justified. A numerical net shortening estimate is not yet supported by an integrated patch. The checked standalone core is not a replacement for the entire 4,934-line affected footprint, and comparison with that footprint would materially overstate the result.

# Share the stored odd rank: 405 / 413 operations

This exact-rewrite sibling preserves the entire polynomial of the frozen
minimal-reflection parent. The source already stores

    R=RankPlusOne-1.

Use `B1=R+RankPlusOne` instead of `B1=1+2R`. The parent 2R product has
only one consumer, and is deleted; all other source and norm gates retain
their exact operators and mapped operands. Every integer input tuple gives
the same complete polynomial value, so every positive witness map and
ordinary source/refutation proof is inherited unchanged.

| Complete tuple | Positive variables | Live operations | Exact degree |
|---|---:|---:|---:|
| original31 | 9 | 405 = 237 mul + 150 add + 18 sub | 1,191,570 |
| compact54-sharp | 9 | 413 = 241 mul + 154 add + 18 sub | 1,316,546 |

The checker imports no producer and executes no historical emitter. It
checks the entire parent/child node inventory, actual R subtraction and
private2R consumer list, every retained operator/operand/leaf, and every
coefficient of both B1 schedules with free RankPlusOne. Schedule induction
then gives pointwise equality of the full output. It additionally repeats
the complete norm/defect identities, all actual fixed coefficient values,
centered degree bounds and nonzero highest homogeneous witnesses modulo
three primes. Six targeted corruptions are rejected for each profile.

```sh
python -B Computability/DiophantineConsistency/research/nine-folded-shared-odd-rank/build.py --check
python -B Computability/DiophantineConsistency/research/nine-folded-shared-odd-rank/check.py
python -B -O Computability/DiophantineConsistency/research/nine-folded-shared-odd-rank/build.py --check
python -B -O Computability/DiophantineConsistency/research/nine-folded-shared-odd-rank/check.py
```

The two checker receipts, four logs and closed manifest are included.
The original and compact tuples remain separate coherent bindings with no
port substitutions. No new native calibration, Lean/internal-ZFC theorem
or optimality claim is supplied. Frozen parents, common documents and the
canonical page remain unchanged.

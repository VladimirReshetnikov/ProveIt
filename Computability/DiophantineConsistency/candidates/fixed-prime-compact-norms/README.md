# Compact fixed-prime norm evaluators

This candidate preserves the complete fixed-prime polynomials and source34 coefficients while replacing their generic Taylor-expanded norm evaluator. The exact generic norm identities save277 operations in each thirteen-variable equation and67 in each fourteen-variable equation.

| Unrestricted integer unknowns | Degree | Live binary operations |
|---:|---:|---:|
| 13 | 1392 | 198 |
| 13 | 1408 | 196 |
| 14 | 652 | 163 |
| 14 | 664 | 156 |
| 14 | 700 | 150 |
| 14 | 748 | 148 |

The useful new fourteen-variable tradeoffs against root-fusion14/696/150 are652/163,664/156 and748/148. The other rows are controls dominated by existing root-fusion evaluators. Every number counts an actual complete stored DAG, with binary addition/subtraction/multiplication charged and fixed numeral leaves free.

See [PROOF.md](PROOF.md) for free-radicand identities, exact whole-prefix substitution and scope. [CHECKS.json](CHECKS.json) and [CHECKS_OPTIMIZED.json](CHECKS_OPTIMIZED.json) record495/20,349-term exact identities, all six whole-circuit degree/liveness checks and operation-preserving mutation rejection. [SOURCE_PINS.json](SOURCE_PINS.json) pins both incoming archives and copied source artifacts. All six actual fixed coefficient payloads are included unchanged.

```
python3 build.py
python3 check.py
python3 -O check.py --output CHECKS_OPTIMIZED.json
```

The parent ordinary proof and calibrated source/native theorem transfer because the entire polynomials are identical. This is ordinary mathematics plus exact Python arithmetic evidence, with no new Lean or internal object-ZFC proof. Lean work is paused. No frozen H10 emitter or numeral array is executed.

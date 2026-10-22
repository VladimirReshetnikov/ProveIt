# Check the archived six-goal shared implication proposal against current sources

The baseline is ProveIt commit `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
The delivered `refactor` files are byte-identical to the archived six-goal
upstream proposal retained under phase twelve's `upstream-merge/inputs/Lean`.
They are attributed prior work, freshly checked here as one part of the
bilingual simplification packet.

The original pair `DominatedImplication.lean` + `Lukasiewicz.lean` contains
42,454 bytes / 811 lines. The delivered pair contains 18,243 bytes / 401 lines.
The numeric `DomRho8` adapter is unchanged. The Tarski namespace tail of
`Lukasiewicz.lean` is byte-identical to the original.

The same 58-detachment plan supplies the unrestricted row, composition,
prefixing, K, Peirce and S. The ordinary calculus uses the universal relation
`True` as domination, so its four basis theorems instantiate the same core.
The core requires no truth constant or implication injectivity.

`check_logic.py` freshly builds 16 project modules in each variant and compiles
the same original-type and axiom-profile audit. Its candidate also checks the
three newly exposed generic basis theorems. It rejects a changed Tarski tail
or changed common audit output. The generic results have no axiom dependencies.
The unchanged numerical and semantic clients retain their recorded profiles.

```sh
python3 check_logic.py --repo /path/to/ProveIt \
  --lean /path/to/lean-4.32.0/bin/lean --out /tmp/k215-logic-check
```

Use a pristine pinned checkout and a nonexistent output directory. The driver
uses the delivered replacements when `refactor/` is present. Its dependency
sources come from the checkout. The full K215 machine endpoint is outside this
focused check.

The source patch applies at the repository root. Incorporation also needs the
maintained generator/plan synchronized with these source files. The exact plan
and its producer are included under `../rocq_shared/upstream/`; rendering its
`--core` output reproduces the delivered Lean core byte for byte.

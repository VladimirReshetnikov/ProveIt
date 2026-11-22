# Quadratic reciprocity in iPRA

Start with **quadratic_reciprocity.pdf**. Sections 1–6 prove the Legendre-symbol product law, the two supplementary laws, and the square-root witness statements. Section 7 gives the primitive recursive terms and quantifier-free induction invariants. Sections 8–9 connect the proof to the two Lean developments.

## Contents

| Path | Purpose |
| --- | --- |
| `quadratic_reciprocity.tex` | Self-contained LaTeX source, including the exact lattice diagram |
| `quadratic_reciprocity.pdf` | Compiled nine-page paper |
| `lean/QRMain.lean` | Checked general reciprocity theorem, integer-valued Legendre symbol and supplements |
| `lean/QRWitnesses.lean` | Least-root search, proof of absence when the scan fails and exponent formula |
| `lean/QREuler.lean` | Unit permutations, Wilson's theorem, Fermat's theorem and Euler's criterion |
| `lean/QRGauss.lean` | Gauss's signed product and Eisenstein's floor-sum parity |
| `lean/QuadraticReciprocity.lean` | Definitions, finite search reflection, modular cancellation, exact rectangle identity |
| `lean/Supplements.lean` | High-count formulas for the negative unit and for two |
| `lean/Involution.lean`, `lean/QRPermutation.lean`, `lean/QRConstructiveList.lean` | Finite-list product, permutation and decidable erasure lemmas |
| `lean/Audit.lean`, `lean/check.sh`, `lean/lean-toolchain` | Reproducible standalone build and transitive axiom report |
| `repo/Goal.lean` | ProveIt object-language statement, reflected residue test and conditional assembly |
| `check.py` | Independent arithmetic checks, including a worked example |

## Reproduction

In the extracted directory, with Lean 4.19.0 on the path, run

```sh
sh lean/check.sh
python3 check.py
```

The Lean script builds nine modules in a fresh temporary directory and then checks the audit file. The direct build uses the Lean 4 standard library and needs no Mathlib download. The fifteen audited endpoints, including `QR.legendre_reciprocity`, `QR.euler_criterion` and `QR.fast_root`, report precisely `propext` and `Quot.sound`. In the signed notation, `QR.legendre p q` means the Legendre symbol of **q modulo p**. Use `QR.legendreZ` for a signed numerator.

The Python checks use only the standard library. The default bound 127 covers 30 odd primes, 1,688 unit residues and 435 prime pairs. An additional run with `python3 check.py --limit 251` covers 53 odd primes, 6,026 unit residues and 1,378 prime pairs. These checks exercise concrete inputs. The Lean statements quantify over all admissible inputs.

With a standard TeX Live installation, rebuild the paper with two passes of `pdflatex`.

```sh
pdflatex -halt-on-error quadratic_reciprocity.tex
pdflatex -halt-on-error quadratic_reciprocity.tex
```

## ProveIt object-language target

The ordinary Lean proof is complete. The accompanying object-language file gives the target `QuadraticReciprocityObject.sentence` and an outline for kernel-checking the iPRA derivation itself. Its assembly takes the Eisenstein sign formula in each orientation and the exact rectangle formula in the prime-pair context. The paper proves each of these and identifies the library modules, recurrence invariants and variable conventions for encoding them.

The overlay was prepared against commit `1e53ba5b26b144afb01bf6774d75cf35f6c760b2`. The available standalone compiler was Lean 4.19.0. The repository's Lean 4.32.0 project and compiled dependencies were unavailable for testing the overlay. In a configured checkout at the pinned revision, the intended command from the repository root is

```sh
lake build IPRADerivations.AnalyticNumberTheory.Primes IPRADerivations.Core.Division IPRADerivations.Core.MultiSums IPRADerivations.Core.ParityArith IPRADerivations.Foundations.BoundedSyntax
lake env lean /path/to/extracted/repo/Goal.lean
```

[ProveIt source at the pinned revision](https://github.com/VladimirReshetnikov/ProveIt/tree/1e53ba5b26b144afb01bf6774d75cf35f6c760b2/Logic/PrimitiveRecursiveArithmetic)

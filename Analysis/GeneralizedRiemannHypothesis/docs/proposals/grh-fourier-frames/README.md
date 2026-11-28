# Fourier frames in the theta-lift proof of Dirichlet GRH

Read **fourier-frames.pdf** for the proofs and source-level integration plan. **fourier-frames.tex** is self-contained and compiles with pdfLaTeX.

The main construction is a frame in the integral theta lattice of bound coprime to the cyclotomic modulus. A correction to each finite Fourier block makes its length detect a single prime. The report also proves a height-counting bound for the spanning argument and a block-column estimate for the discrete-series principal minor.

## Source and verification status

The audited ProveIt revision is `f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f`. All source links in the PDF use this revision. The target files occupy 1,676 physical lines in the readable edition. Net Lean savings have not been measured. The report proves the new mathematical statements. The Lean modules verify parts of the arithmetic construction. Their compiled declarations were replayed with `leanchecker` from their imports. Integrating the new theorems with the GRH project and rebuilding the modified package remain open.

- [Readable Lean development](https://github.com/VladimirReshetnikov/ProveIt/tree/f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f/Analysis/GeneralizedRiemannHypothesis/Lean/grh)
- [Human-readable guide](https://github.com/VladimirReshetnikov/ProveIt/tree/f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f/Analysis/GeneralizedRiemannHypothesis/docs/guide)
- [Compared proposals](https://github.com/VladimirReshetnikov/ProveIt/tree/f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f/Analysis/GeneralizedRiemannHypothesis/docs/proposals)

The proposal directory has Git tree `acf502ce8e6eb1fcd86e1a57f0e4431b956a28d0`. It was also identical at the later main-branch revision `c528b585663a164052c666204f5f0dff3005d1d7`. `results/proposal-comparison.tsv` identifies the subject of every packet. `results/source-audit.json` lists the 43 TeX sources in all 28 packets and anchors claims to exact source contents.

## Reproduce the formal checks

Use Lean 4.35.0 and a Lake project with Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`. From this archive directory run the following command against a prepared checkout. The script creates and cleans up a temporary output directory.

```sh
bash verification/check_lean.sh /path/to/prepared/mathlib4
```

| Lean file | Checked result |
| --- | --- |
| `FourierFrame.lean` | Corrected Gram entry for all dimensions and phases satisfying the root hypotheses, including the outer phase sum. |
| `QuadraticCoefficients.lean` | Evaluation of the quadratic recurrence, trace and norm identities, coefficient reduction and block and sum congruences. |
| `CyclotomicSlope.lean` | Prime-power cyclotomic derivative and its integral identity. |
| `MixedSlope.lean` | Mixed-conductor derivative and the associated-elements identity in every local integral domain of the requisite residue characteristic containing the primitive root. |
| `FrameWitness.lean` | The ultrametric unit equality and both scaled and unscaled integrality estimates. |

`results/lean.txt` records the compiler, axiom reports and replay output. The report connects these results to the number field, its simultaneous weight embeddings and the prescribed level.

## Reproduce the arithmetic and analytic checks

The Python 3 scripts use its standard library. From this directory run

```sh
python3 verification/check_vacuum_frames.py
python3 verification/check_conductor.py
python3 verification/check_archimedean_height.py
python3 verification/check_minor_flow.py
python3 verification/audit_source.py /path/to/ProveIt
```

- `check_vacuum_frames.py` checks Gram entries in an exact cyclotomic polynomial quotient for 12 small conductors and tests the arithmetic at 14 conductors for both coefficient choices.
- `check_conductor.py` checks block entries over a finite field at the parameter-level conductor 4,490,640.
- `check_archimedean_height.py` checks separation on two number fields, including a nonprincipal denominator and every chart pattern at two complex places.
- `check_minor_flow.py` checks second-order principal determinant expansions on exact rational data, uses rational enclosures for logarithms in a second family, and verifies the constants in the ODE bound.
- `audit_source.py` reads committed bytes at the pinned revision, independently of the checked-out branch.

The saved results are in `results/`. The executable checks supplement the universal proofs in the report.

## Build the report

```sh
pdflatex -interaction=nonstopmode -halt-on-error fourier-frames.tex
pdflatex -interaction=nonstopmode -halt-on-error fourier-frames.tex
```

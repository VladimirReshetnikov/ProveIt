# Independent mathematical and implementation review

This is a second AI-assisted proof and implementation review. It is **not external peer review, independent human refereeing, or proof-assistant verification**. No mathematical defect was found in the statements and proof paths listed below. The numerical calculations supplement the written certificates; they do not establish the general theorems.

## Scope of the proof review

- **Complete four-frequency frontier:** checked all seven branches, the transition polynomial and its unique relevant root, positivity of the primal masses, all active moment equations, feasibility of the unused third moment, dual coefficient signs, endpoint agreements, and uniqueness without a symmetry assumption. Independently expanded the first-window mass and moment identities. An exact resultant provides a second check that no unaccounted third-moment crossing occurs on the new branch.
- **General frequency continuation:** checked the support-annihilator calculation, the exact next moment, both slack formulas, monotonicity of the transition parameter, maximality by uniqueness and compactness, the radical junction, and the width and height asymptotics. The first-window theorem remains an explicitly credited prior input.
- **Finite grids:** checked the split-root polynomial, three-mass construction, uniqueness determinant, exact positive gap identity, uniform eventual validity on compact parameter intervals, all aligned semicircle moduli, and the twelve-residue generating expression. Independently derived the four first/second derivative identities used in the semicircle expansion. The finite-grid feasibility tests are substantive and remain explicit in the theorem.
- **Cyclic derivative comparison:** independently derived the circular-window pair-intersection polynomial and its lower bound of one eighth. Checked the strengthened union inequality, all exceptional-increment cases for N at least twelve, and the equality classification. The minimum pair intersection is at quarter separation when N is divisible by four, not at antipodal separation.
- **Opening and applications:** checked that weighted sharpness is distinguished from fixed-cardinality unweighted sharpness, that boundary rounding precedes the second-order grid comparison, that the cycle theorem is restricted to full domains, and that affine-recovery assumptions and the absence of a claimed global Szemeredi improvement are preserved.

## Reproducible optimization checks

The portable driver is `code/verify_fourier_lp.py`. Its dependencies are Python 3, NumPy, SciPy, and SymPy. Run from the package root:

```sh
python code/verify_fourier_lp.py --output data/verification_fourier_lp.json
```

The complete saved record is `data/verification_fourier_lp.json`.

| Check | Scope | Result |
|---|---|---|
| Exact symbolic identities | Quartic dual expansion, the active-moment/dual identity, and the third-moment resultant | All three passed |
| Continuous frontier | 64 radii across every branch, each on a 10,001-point cosine discretization | Maximum observed grid excess 8.95750879026e-09 |
| Aligned semicircle grids | 59 moduli N = 8, 12, ..., 240 | Every formula agreed with the independent LP |
| General finite grids | 663 valid cases, N = 12 through 140, at six prescribed radii | Every formula agreed with the independent LP |
| Exact grid-gap formula | All 663 general-grid cases | Numerical residual below 1e-12 |

The largest observed absolute finite-grid formula/LP difference was 6.66133814775e-15; the verification threshold is 2e-8. The continuous LPs are discretizations and are not exact continuous optimizers. The cyclic-grid LPs use the actual admissible cosine nodes but still run in floating-point arithmetic. Geometric gates and stated numerical tolerances are retained in the driver.

The supplied JSON preserves the two original successful verification runs. Packaging changed only the entry point, output handling, and result grouping; the numerical suites were not repeated after that wrapping change. The portable script was parsed and its command-line entry point checked.

## Additional finite evidence from the cycle review

Direct rational enumeration verified the pair-intersection identity for every N = 2 through 20 and every separation from one through floor(N/2). Exhaustive searches over maps into small cyclic targets supported the proposed sharp comparison below the proved cutoff, but these experiments do not extend the N-at-least-twelve theorem. No claim for the omitted small orders is inferred from them.

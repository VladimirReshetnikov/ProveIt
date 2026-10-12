# Integration notes

## Anchor and placement

This report was prepared against ProveIt commit `73f18ef013d5b74eafc883efb2c15210642df12a`. The six incoming archive interiors present at that revision were inspected for overlap with the selected targets. The mathematical audit is scoped to the dependencies used here, not an exhaustive certification of all repository material.

Place this intact continuation under the existing Polylogarithms report collection, associated with the harmonic-tail and spectral/Stieltjes themes. It also contains a moment-reconstruction section. The current incoming procedure separates archive placement from rewriting the unified manuscript; this package does not prescribe or perform an intake commit.

## New material by section

| Section | Proposed thematic use |
|---|---|
| 2 | Add the complementary square law, continuous-order identity, all-index Stieltjes corollary, and Gamma primitive after the current tail identities. The one-product color compatibility statement applies only to its specified ansatz. |
| 3 | Continue the alternating rational-tail generator to all cyclotomic colors and arbitrary outer character. Record the parity/conjugation sector explicitly. Keep the cutoff proof and the trivial-color pole cancellation. |
| 4 | Resolve Quadratic-Spectrum Stieltjes further-research question 2 with the all-order polynomial-weight defect. Preserve the extra resonant term `r! alpha[k,r+1]/2`. |
| 5 | Add the ordinary Gamma integral for the second correction, shift/distribution rules, and every anchored shift primitive. This advances the negative-integer-jet and mixed-primitive questions, without establishing minimality of a function algebra. |
| 6 | Resolve the second-derivative and confluence objective of Quadratic-Spectrum Stieltjes question 7 for all even polynomial weights and any number of factors. Pair shifts `a` and `1-a` to obtain the bilateral version. |
| 7 | Strengthen the inherited order-eight theorem and add the new order-ten theorem, with explicit residue exclusions. Preserve the formal-coordinate interpretation and the contraction thresholds. |
| 8–9 | Update the claim status, retain existing source corrections, and attach the concrete research programme and reproducibility evidence. |

## Source questions whose status changes

- **Shifts and Twists Q6:** the explicit higher-conductor generator objective is resolved for the prescribed parity sector, including conductor four. This does not reduce the complementary sector.
- **Quadratic-Spectrum Stieltjes question 2:** the higher-jet defect is explicitly computed for every polynomial weight and every spectral derivative order.
- **Quadratic-Spectrum Stieltjes question 7:** the complete second derivative and all coincident-mass coefficients are computed in the even-polynomial setting.
- **Polygamma Reconstruction and Resonance, order-eight prefix:** replace the remaining exclusion `b = 1 mod 16` by `b = 8001 mod 16384` when citing this stronger theorem.
- **Polygamma Reconstruction and Resonance, unequal-order programme:** add the order-ten family outside `b = 962 mod 2048`. The general question remains open.

## Claims that must remain open or qualified

- The global gap-six and arbitrary unequal-order moment-prefix problems are not proved.
- The excluded order-eight and order-ten progressions are limitations of the congruence theorem, not evidence of singular matrices.
- The Gaussian weight-six and revised weight-eight numerical conjectures remain unresolved. The new Gaussian tail evaluations concern different sums.
- Formal rank concerns basis labels before numerical evaluation. It is not arithmetic independence of zeta values.
- The classical colored parity theorem and the existing first-derivative anomaly are inherited foundations, not claimed discoveries.
- The independent shifted-tail objective of Shifts and Twists Q4 is not resolved by factoring a single tail denominator into `(k+a)(k+b)`.
- Independent tail-order/weight jets, the third degree-generating variable, and the specific depth-three colored primitive in Shifts and Twists remain separate open targets.
- No generic finite classical-polylogarithm reduction of the new Gamma/logarithmic kernels is asserted. The exact integral representations are complete identities without a minimality claim.

## Corrections and conventions to preserve

The targeted audit found no additional false theorem in the current dependencies. Retain the two corrections already present in `chapters/11-stieltjes-source-corrections.tex`: the missing initial Hurwitz–Stieltjes term and the sign of a literal Laurent coefficient. They were already established by the current manuscript and are not new findings here.

In every new formula, use `zeta(1+u,a) = 1/u + sum (-1)^r gamma_r(a) u^r/r!`. Keep ordinary convergence separate from spectral continuation. In particular, the continuous-order square identity is ordinary for `Re s > 0`; at `s = 0` the finite upper endpoint supplies a nonzero quarter. Low-order weighted confluent coefficients use continued zeta values when their unmodified sums diverge.

The moment contraction needs `b >= 2a`; the order-ten generic formula must not be used below `b = 10`. All small cases needed in the theorem are calculated from the original source matrix. The forward `D`-to-`C` transform has diagonal `2j+1`, while its displayed inverse has diagonal `1/(2r+1)`.

## Evidence and formal status

The written proofs establish the analytic claims. The delivered scripts reproduce finite algebra and independent decimal diagnostics. The rank verifier reconstructs exact multivariate determinants, not fitted polynomials. No new theorem is claimed to have a Lean declaration or any other proof-assistant formalization.


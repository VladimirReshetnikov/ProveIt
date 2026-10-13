# Stieltjes reflection and zero-Mellin reconstruction audit

12 October 2026 (Pacific). This milestone follows the request to prioritize generalized Stieltjes functions gamma_n(a), the conventional Laurent coefficients of Hurwitz zeta. All original incoming evidence remains unchanged.

## Attribution and acceptance boundary

The joint reflected convolution algebra is already proved in the preserved `reports/stieltjes-correlation-calculus/continuations/convolution-calculus/Stieltjes_Convolution_Calculus.tex`, in its joint-algebra subsection (lines 663-694 at the inspected source). The canonical section restores that proof with the existing `stconv:calculus-report` citation. The shifted pair closure was already canonical. The many-factor analytic generator, its neutral total-order restriction, and the all-index alternating binomial correlation identity are developed as extensions. No claim of historical priority follows from this bounded source review.

The positive-integer filtered Mellin identity is exactly the specialization `bsm:eq:raw-only` of `bsm:thm:mixed` in the preserved `balanced-stieltjes-moments/article/Balanced_Stieltjes_Moments.tex`, Section 7. Its stronger two-variable logarithmic-moment theorem remains in the original report. The present chapter supplies an independent cancelled-Laplace proof on the open Mellin strip and attributes the integer specialization. It does not claim to have integrated the report's separate balanced profiles, root families, or all logarithmic derivatives.

The zero-Mellin raising identity, single digamma reconstruction with an essential even-index correction, and finite translation-operator reconstruction are the new endpoint extension in this manuscript. Targeted searches of the preserved correlation corpus and relevant portions of primary integral literature found no exact duplicate; they do not establish worldwide novelty.

Classical sources: DLMF 25.11.9 (Hurwitz Fourier formula), 25.11.25 (Laplace integral), 25.11.14 (Bernoulli values), and 25.11.18 (Lerch identity). Independent overlap review also inspected relevant portions of Connon's arXiv:0906.0277, 0902.2188, 1104.1911, and 1801.05711. These are background/overlap checks, not evidence that every statement in those papers was audited.

## Proof obligations checked independently

* The convolution identity is I=delta_0-1. Both Fourier branches are required to prove faithfulness, and the zero Fourier coefficient rules out substituting delta_0 for I. Reflection sends X to Y and X-Y has multiplier -i*pi*sgn(k).
* The many-factor sine/Gamma formula is holomorphic at total order S=0 after combining the terms. Pairing Fourier coefficients with smooth test functions justifies local parameter expansions. Neutral coefficients lie in span(I,X-Y); pointwise coincident products are not asserted.
* Alternating correlations use the existing J_mn normalization. Their contact term restricts to a negative constant off the integer lattice. The even-index zeta term and odd reflected sign are indispensable.
* For positive shifts and annihilation of powers 0 through r-1, Q(t)=sum(c_j exp(-a_j t))/(1-exp(-t)) is O(t^(r-1)) at zero and decreases exponentially at infinity. This proves absolute Fubini and all fixed parameter derivatives on 0<Re(v)<r near spectral order one.
* At integer Mellin k<r, the Bernoulli polynomial of degree k is annihilated. The zero cancels the Gamma pole before differentiation; it need not be a simple zero.
* The zero endpoint requires only sum(c_j)=0. Subtracting F_n(0) on (0,1) yields an ordinary integral, with tail O(x^-1 log^n x) before division by x. Changing the split to rho changes the answer by -F_n(0) log(rho).
* Digamma reconstruction is the finite coefficient identity obtained by multiplying the meromorphic Mellin germ by sin(pi*v)/pi. Its even-index term comes from the removed pole; omitting it fails the exact adjacent-shift control.
* The translation operator preserves the algebraic span of the shifted Stieltjes functions. Its finite reconstruction is coefficientwise. No convergence in operator norm, infinite iterated-integral interchange, interval certification, Lean verification, or arithmetic independence is claimed.

## Reproducible evidence

`check_stieltjes_reflection_algebra.py`: 7 exact normal forms, 56 polarized generator coefficients across two Fourier branches, and 4 negative controls.

`check_stieltjes_neutral_reflection.py`: 18 alternating identities (indices 0 through 8, both branches), 54 neutral-family coefficients, and 3 negative controls.

`check_stieltjes_mellin_exact.py`: 58 exact identities, including sine reconstruction, kernel polynomials, Gamma-quotient raising, elementary adjacent-shift controls and finite operator reconstruction; 4 rejected corruptions.

`check_stieltjes_mellin_numeric.py`: 44 floating-point comparisons, comprising 22 digamma-only reconstructions, 4 transformed raising integrals and 18 previously supplied resonant identities. The reconstruction includes a 50/70-digit refinement and an adjacent-shift case. Each recorded absolute error is below 1e-40. Stable Taylor/asymptotic expansions only avoid cancellation in digamma point evaluation; these computations are diagnostics, not interval bounds.

The numerical implementation evaluates reconstruction through digamma, independently of the reference Stieltjes implementation. The raising and positive-integer checks use one-dimensional Laplace integrals to avoid nested Stieltjes quadrature. The written analytic proofs establish all-index validity; finite outputs test coefficients, signs, normalization and implementation.

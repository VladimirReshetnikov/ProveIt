# ProveIt source inventory and selected extension

Inspected commit: `dedc2966ea6f59cc0a8fd0327d68cda31bce6df1` (commit date 2026-11-27 00:17:04Z; client date 26 November 2026).

The project README explicitly says the research packets were placed as delivered, not independently checked or formalized; their Lean files are not part of ProveIt's root Lake package. The current Research tree includes 61 first-batch and 42 second-batch packets.

## Files actually read

### prime_peak_rigidity/prime_peak_rigidity.tex

Blob: `86d638f10b5f233a1201c4434e7dd1444c6f43fa`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/prime_peak_rigidity/prime_peak_rigidity.tex

Positive phase-energy formula; exact identity-class peak; uniform translate control from a near peak; symmetric-class linear deficit; universal recurrence sequence. Explicit unresolved problem: effective near-peak return lengths and other kernels.

### prime_scale_coalescence_2026-11-26/prime_scale_coalescence.tex

Blob: `86d1afd6bf95e97fae5ca2b456d3f96fe387838d`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/prime_scale_coalescence_2026-11-26/prime_scale_coalescence.tex

Scalar coalescence eigenvalue scales 1, ε², ε³ log(1/ε); local squared-multiplicity control using Montgomery; finite difference and optimal prediction saturation. Full mixed-character coalescence remains distinct.

### grh_prime_error_balancing/report.tex

Blob: `ad79520aede37acb13e09936f544e78cfe21d75e`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/grh_prime_error_balancing/report.tex

Uniform convex balancing; common compact probability convolution annihilator. It takes one Unif[-π/γ,π/γ] factor per low zero; support O(log² B), tail exp(-cB logB). The present theorem improves support to O(log B).

### grh_spectral_rigidity/spectral_rigidity.tex

Blob: `2a92173c4e59b190b79587bbecd6788f8a0c3ff6`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/grh_spectral_rigidity/spectral_rigidity.tex

Polynomial zero-divisor rigidity and high-pass jet covariance, including arbitrary finite frequency deletion. Differential polynomial coefficients are already treated without delays.

### prime_power_rigidity/prime_power_echoes.tex

Blob: `1b455ee455394be0188bb3ed2d2d3916160faa64`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/prime_power_rigidity/prime_power_echoes.tex

Prime-power kink recovery via three cutoff observations; universal near-zero metric cusp; path components; all unlabelled metric isometries and modulus equivalence q~2q for odd q. A simple cusp/metric-dimension extension would have little novelty.

### grh_multiscale_covariance/report.tex

Blob: `56e3944ef8bbb444b5e0fd06d169d4c57cf99910`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/grh_multiscale_covariance/report.tex

Arbitrary finite real shifts, all residue classes, finite spectral deletions: covariance is strictly positive. The proof already uses translated prime atom isolation via the distributional explicit formula.

### multiscale_prime_fluctuations/paper.tex

Blob: `3ba1fe31f67d7fece15ba84ffbe77db1d381c914`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/multiscale_prime_fluctuations/paper.tex

Stronger quantitative shifted coercivity on every zero band (T,T+H], KlogT≤H≤T: lower cH/(T⁴logT), upper CHlog²T/T⁴. Uses Landau probe sums to recover every scale/class coefficient.

### grh_multiscale_prime_fluctuations/report.tex

Blob: `af41eb3f0638230c0a303372b672a3dc25175763`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/grh_multiscale_prime_fluctuations/report.tex

One-sided multiscale prime-error moment abscissa equals supremum zero real part; sharp critical logarithmic power threshold; integer product criteria.

### grh_new_results_2026-11-26/sections/surgery.tex

Blob: `b94f13ee67d5dbabb11fbf98dfbe2f8df1d41644`.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/dedc2966ea6f59cc0a8fd0327d68cda31bce6df1/Analysis/GeneralizedRiemannHypothesis/Research/grh_new_results_2026-11-26/sections/surgery.tex

Finite-jet surgery of even real entire functions preserves finitely many Taylor/log coefficients and eventual zero count while creating any prescribed finite multiplicity at large ordinate.

## Selected substantial extension

The positive Fourier annihilation theorem in annihilation_theorem.tex improves the existing compact average support from O(log² B) to optimal-order O(log B), preserving exact annihilation at all low Dirichlet zero ordinates and attenuation exp(-c B log B) of every higher real frequency. It enforces aggregate multiplicities as well. The proof uses a positive separated-set interpolant, local-count coloring, convolution, and a final uniform-density convolution for tail damping. Jensen gives lower radius (1/2)log B+O(1) if multiplicities are preserved for zeta; Montgomery's proved pair formula gives (5/12-o(1))log B even for distinct-only cancellation. The arithmetic consequence changes the available scale window from X exp(±O((loglog X)²)) to X(log X)^{±O(1)} with error X^{-1}(log X)^{O(1)} for the explicitly sqrt-weighted prime-error average.

## Literature and novelty status

- Primary prior art: J. Florek, *Interpolation by the Fourier–Stieltjes transform of a positive compactly supported measure*, Colloquium Mathematicum 54 (1987), 113–120, DOI 10.4064/cm-54-1-113-120. Official metadata at https://www.impan.pl/en/publishing-house/journals-and-series/colloquium-mathematicum/all/en/publishing-house/journals-and-series/colloquium-mathematicum/all/54/1/105540/interpolation-by-the-fourier-stieltjes-transform-of-a-positive-compactly-supported-measure . Download returned 403. The generic possibility of positive Fourier interpolation must therefore be credited to the classical literature, not presented as a new idea.
- H. L. Montgomery, *The pair correlation of zeros of the zeta function*, 1973, original paper: https://public.websites.umich.edu/hlm/paircor1.pdf . Equation (6) on printed p.182 and the argument on printed pp.191–192 imply M2(T)≤(4/3+o(1))N(T) under RH. Only the proved range 0<α<1 is used, not the conjectural pair correlation.
- Targeted searches for positive measures with prescribed Fourier zeros, compact Dirichlet/zeta zero annihilation, interpolation, and logarithmic support did not locate this exact quantitative arithmetic package. This is a candidate new theorem and explicit improvement over the supplied packet, not a verified historical priority claim.

## Audit cautions

1. Do not call arbitrary-shift covariance or translated prime-atom isolation new; both appear in the inspected current packets.
2. Do not call near-zero cusp, arithmetic metric rigidity, or universal peak recurrence new; these appear in inspected current packets.
3. Optimal support is claimed in order, not leading constant. The constructed bound is not numerically better at every small cutoff.
4. Central zeros cannot be annihilated by a probability kernel and must remain as bias.
5. Finite numerical tests of approximate zeros do not prove exact cancellation; the analytic theorem is exact, and the stated frequency-perturbation inequality bounds numerical errors.
6. The arithmetic result is a positive weighted average, not a pointwise prime-error improvement.


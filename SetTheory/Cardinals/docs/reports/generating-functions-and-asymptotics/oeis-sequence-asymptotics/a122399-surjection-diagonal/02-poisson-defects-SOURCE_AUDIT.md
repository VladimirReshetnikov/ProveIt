# Source and dependency audit

Prepared 4 October 2026. All links below are sources, not evidence of endorsement or independent review.

## Repository anchor

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected tree commit:

    0f93381e8932d3aee3d5c2abfb5c98d128d49b9c

Report directory:

    SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/
    oeis-sequence-asymptotics/a122399-surjection-diagonal

File: `proof.md`, Git blob:

    6f03a8be2d313d67cebce8a5f5f641bbb78e08d1

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/0f93381e8932d3aee3d5c2abfb5c98d128d49b9c/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a122399-surjection-diagonal/proof.md

Title: *A122399: a complete saddle expansion, an exact vertical contour, and quantitative inversion*, dated 1 October 2026.

The report proves a fixed-direction all-order expansion uniformly on compact subsets of positive m/n, and a diagonal block-count central limit theorem. It explicitly does not assert boundary-uniform asymptotics or a local limit theorem. Its exact rectangular definition and the gaps in its scope motivated the present work.

The repository connector search `A122399 Poisson`, scoped to this repository, returned the earlier report's Poisson-summation contour argument, not a defect-Poisson transition. This is scoped nonduplication evidence, not an exhaustive absence proof. Other OEIS reports were screened during topic selection but are not mathematical dependencies here.

## OEIS

https://oeis.org/A122399

The definition and first fifteen integers were checked. The entry already records a diagonal growth constant (2013) and leading asymptotic equivalent (2018), attributed to Vaclav Kotesovec. Neither is claimed as new. The modular-period conjecture in the entry is not the target of this article; the prior repository report already discusses it.

https://oeis.org/A317855

Associated growth constant. Used only for provenance and comparison with the prior report.

## Classical primary sources

1. Lily L. Liu and Yi Wang, *A unified approach to polynomial sequences with only real zeros*, Advances in Applied Mathematics 38 (2007), 542–560. https://arxiv.org/abs/math/0509207

   Context for root interlacing. The exact recurrences and Rolle proof needed here are written out in full, rather than delegated to an unverified theorem application.

2. Lucien Le Cam, *An approximation theorem for the Poisson binomial distribution*, Pacific Journal of Mathematics 10(4) (1960), 1181–1197. https://doi.org/10.2140/pjm.1960.10.1181

   Primary PDF: https://msp.org/pjm/1960/10-4/pjm-v10-n4-p11-s.pdf

   Theorem 1 and its convolution proof, pp. 1183–1184, were inspected, including page images. The article reproduces the elementary probability argument for the bound it uses. Poisson approximation for Bernoulli sums is explicitly classical.

3. Jessica Khera, Erik Lundberg, and Stephen Melczer, *Asymptotic enumeration of lonesum matrices*, Advances in Applied Mathematics 123 (2021), 102118. https://arxiv.org/abs/1912.08850

   Nearby bivariate enumeration and asymptotic methods. Its lonesum-matrix family is different from the rectangular surjection array here. The article does not identify the two denominators or transfer theorems between them without proof.

## Dependency boundary

Self-contained in this manuscript:

- Defect coefficient identity and domination.
- Integer-exponent root location and exact Bernoulli representation.
- Finite count, moment, and total variation estimates.
- Qualitative trichotomy for all integer n(m).
- Uniform local Edgeworth theorem at exact cumulants.
- Critical-window all-order power-log expansion and its remainder.
- Inverse critical expansion, including its root-error estimate.
- Exact integer certificate for N_(1/e)(1000)=6207.

Inherited analytic input only for the diagonal specialization in Section 10:

- The prior report's saddle equation and constants for the diagonal mean and variance.

The finite tests do not replace the analytic arguments. In particular, observed degree patterns beyond the proved degree bound remain questions, and the numerical order-4 successes do not establish large-order or beyond-all-orders properties.

## Novelty and status

The exact boundary formulas and estimates are presented as derived extensions of the inspected repository report. No comprehensive literature search can be inferred from these targeted inspections, and no claim of globally established priority, a famous conjecture settlement, or a new general method is made. The manuscript is unrefereed and not formally verified. No external write, pull request, or OEIS submission was made.

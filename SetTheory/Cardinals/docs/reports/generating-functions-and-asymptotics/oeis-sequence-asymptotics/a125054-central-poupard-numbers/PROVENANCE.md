# Provenance, attribution, and verification boundaries

Date of investigation: 1 October 2026.

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned inspected commit: `ef66df0fdb8fc64cbc80756d622cab0e8e85e262`.

The repository tree and root README were inspected through the connected GitHub read interface. Repository code searches for the literal identifiers `A125054` and `A000182` returned no matches in the inspected results. A Lambert-related search located the methodological predecessor described below. Neither search-index coverage nor the full research corpus was exhaustively audited.

Methodological predecessor, README inspected at the pinned commit:

https://github.com/VladimirReshetnikov/ProveIt/blob/ef66df0fdb8fc64cbc80756d622cab0e8e85e262/Analysis/Transseries/docs/series-and-transseries/Logarithmic_Critical_Endpoint_Lambert_Charts/README.md

Title: *The Logarithmic Critical Endpoint: Convergent Lambert Charts, All-Order Sector Laws, and Sharp Action-Cutoff Corrections* (29 September 2026). That report treats a countable-action implicit equation. Its README was used as methodological context for all-order expansions, inversion, and explicit trust boundaries. The present article treats a different moment-integral model and does not import any theorem from that report or claim to have audited its complete source or proofs.

During the investigation, an additional read of the current main commit returned `dc1a7242d2ab4a4496b7dfee63256ee767b21fc9`, dated 2026-10-01T18:13:49Z. The earlier snapshot was retained for provenance. No repository write, commit, pull request, or other mutation was made.

## Inspected primary sources

1. OEIS A125054: https://oeis.org/A125054
   The returned entry identifies the central Poupard sequence, its tangent binomial transform, a leading asymptotic attributed to Vaclav Kotesovec (30 May 2015), the 3-valuation observation of F. Chapoton (2 August 2021), and the continued-fraction conjecture of Peter Bala (15 December 2025). The proposed fraction has successive internal weights 9, 8, 25, 24, 49, 48, ... . The observed labels are reported as labels in the inspected entry, not a proof that no prior proof exists. The entry returned by web retrieval was cached; this investigation does not certify the state of every later OEIS revision.

2. OEIS A125053: https://oeis.org/A125053
   The parent triangle, row construction, relation to tangent and secant numbers, and references to Foata and Han. Its listed row data provided an independent finite recurrence check.

3. OEIS A000182: https://oeis.org/A000182
   Tangent-number normalization. The article uses T_n = (2n+1)! [z^(2n+1)] tan(z), starting 1, 2, 16, 272, ... .

4. OEIS A000364: https://oeis.org/A000364
   Secant-number normalization for a second shifted-moment example.

5. Dominique Foata and Guo-Niu Han, *Finite Difference Calculus for Alternating Permutations*, arXiv:1304.2483 (2013).
   https://arxiv.org/abs/1304.2483
   https://arxiv.org/pdf/1304.2483
   The paper's Poupard generating function and finite-difference structure are prior results. The report reproduces the short diagonal-operator calculation needed for its specialization.

6. Peter Bala, *Some S-fractions related to the expansions of sin(ax)/cos(bx) and cos(ax)/cos(bx)*, 11 May 2017.
   https://oeis.org/A002439/a002439.pdf
   Prior continued-fraction machinery, including contraction and binomial-shift operations. The report supplies the all-index formal manipulations with its own indexing. The 2025 identity being proved is the later displayed OEIS conjecture, not a claim to discover the 2017 framework.

7. NIST Digital Library of Mathematical Functions:
   - https://dlmf.nist.gov/4.22 — trigonometric products and partial fractions.
   - https://dlmf.nist.gov/5.11 — Stirling asymptotics.
   - https://dlmf.nist.gov/2.3 — Laplace asymptotics for real integrals.
   - https://dlmf.nist.gov/4.13 — Lambert W.
   - https://dlmf.nist.gov/1.10 — complex analytic tools.

These sources are cited in the article. No complete third-party source is reproduced in the package.

## Claims and attribution

The two concrete OEIS statements have self-contained all-index proofs in Sections 3 and 4. The congruence a_n = 3 modulo 9 implies the observed valuation statement and is stronger.

The tangent and Poupard generating functions, classical fraction identities, and already-recorded leading asymptotic are not presented as new. The structural positivity and determinant consequences are explanatory material, not priority claims.

The further theorems developed in this report concern exact exponential sectors with remainder control; a uniform all-order endpoint-saddle expansion for a growing shift; coexistence and Gaussian/mixture laws; a general p > 1 shifted-moment transition; complex zeros deduced from positivity and the real transition; and fixed-shift inversion including an exponential correction. Targeted literature searches did not identify an exact publication matching the complete package. That is not an exhaustive novelty determination, especially because related results may use different terminology. No assertion of worldwide priority or a field-wide breakthrough is warranted solely by these searches.

The full all-order expansion is specific to the tangent model. The universal theorem under an O(1/y) tail assumption gives a leading transition with the explicitly stated error; it does not assert an unjustified universal all-order tail expansion. Complex zero locations are for each fixed index j, not j increasing with the polynomial degree. No global zero distribution is claimed.

## Computational record

`code/verify.py` is supplied source code written for this report. It uses no network access, no external data files, and no random selection in its checks. The initial 17 OEIS values are embedded only for a finite normalization check. All further exact values used in finite tests are generated by the tangent recurrence or the independent Poupard row recurrence.

The full delivered run used `--max-n 4096 --dps 90`. Package and interpreter versions are recorded in `data/verification.json`; output is in `data/verification_run.txt`. That stdout retains the working-directory path of the executed run. It does not imply the existence of that path on another machine.

Exact integer and symbolic operations must be distinguished from high-precision floating-point diagnostics. A root residual below 10^(-55) does not certify its location or uniqueness. Theorem 11.1, not the residual, proves the eventual simple-zero assertion. The printed transition constants are numerical approximations to exact definitions, not interval-certified decimal bounds.

The mathematical proofs were developed and checked in this session; they have not received independent peer review. There is no Lean formalization, no machine-checked analytic proof, and no interval-arithmetic certification. `BUILD_REPORT.json` records the performed file, build, replay, and visual checks, not an independent validation of every mathematical argument.

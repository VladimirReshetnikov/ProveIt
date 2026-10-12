# Proposed integration into ProveIt

This note accompanies **Bilinear Tail Identities, Polylogarithmic Resonances, and Stieltjes Boundary Products** (11 October 2026). It proposes a landing plan and precise status updates. It does not apply changes to the repository.

## 1. Authoritative source state

The current source pin is commit `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`, timestamp **2026-10-11 21:44:07 UTC**:

- [Pinned unified manuscript](https://github.com/VladimirReshetnikov/ProveIt/tree/da2792fc9cc8ef19c6a314be6c65e1437fbdc66b/Analysis/Polylogarithms/docs/manuscript)
- [Pinned incoming directory](https://github.com/VladimirReshetnikov/ProveIt/tree/da2792fc9cc8ef19c6a314be6c65e1437fbdc66b/docs/incoming)

The five incoming packages at that pin are `ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11.zip`, `ProveIt_Finite_Difference_Determinants_2026-10-11.zip`, `ProveIt_Higher_Quadratic_Jets_2026-10-11.zip`, `ProveIt_Higher_Spectral_Defects_2026-10-11.zip`, and `ProveIt_Quartic_Spectral_Reconstruction_2026-10-11.zip`. Their chronology must not be inferred just from the shared date. The delivery's `provenance/sources.json` records source paths and selected passages; the rank source-input manifest records SHA-256 hashes of the exact dependencies used in the finite certificates.

An earlier archived source is needed to identify the Stieltjes research question accurately. It is **not** one of those five current incoming packages:

- Repository path: `docs/incoming/ProveIt_Polygamma_Tail_Identities_2026-10-11.zip`.
- Archive-containing commit: `446dca9bd65c20e409d1d2561d4ffad408103e2a`.
- [Immutable archived source](https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/446dca9bd65c20e409d1d2561d4ffad408103e2a/docs/incoming/ProveIt_Polygamma_Tail_Identities_2026-10-11.zip).
- ZIP SHA-256: `2d166836af1978fdf08519a33eb3953f1198530bb9a55d7ebba7ca418666c0e0`.
- Git blob SHA-1: `a059f21f0b26ea1c628ba26b1f2c50f75567c46e`.
- Size: 687622 bytes.
- The report itself cites baseline `f7e35be357654198c1546fd40f363694c5bcc2cc`. This is its own research baseline, **not** the commit containing the archived ZIP.
- Research target: inner `sections/09_audit_research.tex`, paragraph 9, “Generalized Stieltjes products at the missing derivative edge.”
- Inherited positive-positive theorem: inner `sections/06_hurwitz_products.tex`, label `hprod:stieltjes-products`.

The classical Hurwitz product input should be cited to M. A. Shpot, M. P. Chaudhary, and R. B. Paris, *Integrals of products of Hurwitz zeta functions and the Casimir effect in φ4 field theories*, *Journal of Classical Analysis* **9**(2) (2016), 99–115, DOI [10.7153/jca-09-11](https://doi.org/10.7153/jca-09-11), Remark 1. Retain all three authors. The product identity itself is classical; the newly supplied result is the missing-edge subtraction and its all-index finite-part consequences.

## 2. Suggested landing plan

The first repository landing can be the intact delivery ZIP at:

`docs/incoming/ProveIt_Tail_Kernels_and_Boundary_Products_2026-10-11.zip`

The following filenames are **proposed new files**, not claims that such files already exist. Paths in this table are relative to `Analysis/Polylogarithms/docs/manuscript/`.

| Delivery section | Proposed manuscript landing | Placement and dependency |
|---|---|---|
| `sections/02_bilinear.tex` | `chapters/07-bilinear-tail-certificates.tex` | Near the harmonic-tail and centered-polygamma material. Preserve the explicit recurrence and certificate class before stating the factorization criterion. Cross-reference the incoming alternating-tail report. |
| `sections/03_shifted_kernels.tex` | `chapters/07-independent-shift-tail-kernels.tex` | Immediately after the preceding insert. Include both kernels, their finite endpoints, rank identity, mixed derivatives, and the anchored Gamma–Hurwitz primitive together. |
| `sections/04_mellin.tex` | `chapters/07-polylogarithm-mellin-resonances.tex` | After the integration foundations in `chapters/07-integration.tex`, or at an equivalent point before the general integral-jet material. Preserve the joint holomorphy lemma and the complete neighboring-order combination. |
| `sections/05_stieltjes_edge.tex` | `chapters/07-stieltjes-positive-derivative-edge.tex` | After `chapters/07-shifted-stieltjes-correlations.tex`. Cross-reference `chapters/08-stieltjes-contact-products.tex` and `chapters/08-periodic-collision-contacts.tex`; do not replace them. |
| `sections/06_order_ten.tex` and `sections/07_order_twelve.tex` | `chapters/07-moment-prefix-orders-ten-twelve.tex` | Near `chapters/07-centered-trigamma-moments.tex`, once the formal coordinate definitions and inherited normalization results are in scope. The delivery includes the coordinate-space definition needed to avoid an undefined-rank assertion. |
| `sections/08_audit_and_research.tex` | A new continuation-audit section, or selected entries in the current research-status chapter | Merge status statements carefully. Keep the remaining unrestricted rank and gap-six questions explicit. |
| Exact programs, certificates, and replay outputs | `verification/tail_kernels_boundary_products/` | Proposed new verification directory. Keep the arithmetic certificates and source-input manifest beside their verifiers. |

When splitting the standalone article, convert its bibliography entries and labels to the unified manuscript's naming convention. The current article uses `bi:`, `sh:`, `mpr:`, `edge:`, `t10:`, `t12:`, and `audit:` prefixes. Inspect the destination for collisions before adding `\input` statements. Keep all domain hypotheses and the fixed-coordinate finite-part convention with the theorem statements; moving only displayed evaluations would lose necessary mathematical content.

## 3. Exact status edits

### Quartic reconstruction report, research question R1

Source: current incoming `ProveIt_Quartic_Spectral_Reconstruction_2026-10-11.zip`, inner `sections/08_research.tex`.

Proposed replacement status:

> The complete smaller-order-ten and smaller-order-twelve families are now proved: the first-q prefix has full formal coordinate rank for every even q greater than 10 and greater than 12, respectively. Order ten follows from the prior congruence theorem, the prior eventual threshold, and one remaining exact determinant. Order twelve follows from an explicit eventual threshold and a complete independently replayed finite-field certificate. The unrestricted unequal-even-order problem remains open.

Use article labels `t10:complete` and `t12:complete`. Preserve attribution of the prior results:

- Alternating-tail report, inner `sections/07_rank_refinement.tex`, theorem `rt:rank10`: the order-ten family outside the progression `b = 962 mod 2048`.
- Quartic report, inner `sections/03_eventual_rank.tex`, theorem `ert:main` and its normalization results.
- Quartic report, `verification/eventual/eventual_threshold_a5.json`: the exact threshold `B_5 = 1920`.
- The general leading homogeneous determinant factorization, Bernoulli transformations, Padé contraction, and source coordinate reconstruction are inherited mechanisms.

Only `b=962` remains after intersecting the order-ten source results. The original matrix determinant is `15578 mod 65537`; the retained five-square determinant is `60407 mod 65537`.

For order twelve, every `b >= 11520` is covered by the written threshold proof; all 11513 integers `7 <= b <= 11519` have certified nonzero determinant residues. Do not describe this as sampling or as a numerical rank computation.

**Do not mark solved:** quartic R2 (all `a<b`), the entire fixed-gap-six family `b=a+3`, or the unresolved Gaussian `S_6` and revised `S_8` identities. The new families include `(p,q)=(10,16)` and `(12,18)` but do not imply the complete gap-six assertion. Formal coordinate rank is not arithmetic independence.

### Alternating-tail report, bilinear adjacent-tail question

Source: current incoming `ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11.zip`, inner `sections/08_audit_and_research.tex`, question headed “Bilinear adjacent-tail certificates.”

Proposed replacement status:

> The rational two-adjacent-product certificate class is completely classified. A nonzero rational coefficient pair exists exactly when `t^2 alpha beta = 1` and `P(z)/Q(z) = rho h(z)h(z+1)` with h rational. The divisor criterion decides this factorization, and exact finite endpoints give two kernels for independently shifted adjacent quadratic denominators. Larger support, incompatible denominator pairs outside this certificate class, and independently variable Hurwitz orders remain open extensions.

Use labels `bi:classification`, `bi:divisor`, `bi:sum`, `sh:two-kernels`, `sh:mixed`, and `sh:primitive-theorem`. The prior one-product ansatz was not erroneous; the new theorem answers the explicitly requested enlargement. A nonexistence statement within this ansatz must not be restated as a theorem that no closed summation identity exists.

Here “nonzero” means that the rational coefficients A and B are not both zero. The evaluated certificate or its resulting weight can vanish on a special locus such as coincident shifts. Do not strengthen the statement to require a nonzero evaluated sum for every parameter choice.

### Earlier missing Stieltjes derivative edge

Source: the immutable older polygamma archive identified in Section 1, paragraph 9 of its research section.

Proposed replacement status:

> The missing same-point quadratic edge with exactly one zero argument-derivative order is now proved by a jointly subtracted Hurwitz kernel. Together with the previous positive-positive result, this gives a finite ordinary-zeta derivative formula for every positive total argument-derivative order. The double-undifferentiated corner is inherited and its normalization is checked. Nonzero periodic-translation products and the contact-term tower retain their earlier proofs and attribution.

Use labels `edge:theorem`, `edge:uniform-dictionary`, `edge:endpoint`, and `edge:corner`. The old source request mentioned one or both zero derivative orders; make clear that the newly proved component is the positive-total edge, while the double-zero component is reconciled with an existing theorem.

Canonical inherited source anchors:

- `chapters/07-shifted-stieltjes-correlations.tex`, theorem `scoll:thm:coincident` and equation `scoll:eq:J00` for the coincident undifferentiated finite part.
- `chapters/08-stieltjes-contact-products.tex`, theorem `shj:contactthm` and its equation `shj:generalcontact` for translated derivative products, and corollary `stconv:cor:fulltower` for the differentiated convolution tower.
- `chapters/08-periodic-collision-contacts.tex` for the existing fixed-coordinate quadratic collision law.

The identity `FP integral_0^1 gamma_0(x)^2 dx = 2 gamma_1 - pi^2/3` is inherited. The new positive-total dictionary uses order derivatives only at `w=r+t+1`; its coefficients contain ordinary zeta values at other positive integers. Avoid the stronger and incorrect wording “all zeta values occur only at w.”

## 4. Mathematical conventions that must travel with the results

1. Use `zeta(1+u,a)=1/u+sum((-1)^m gamma_m(a) u^m/m!)`, so `gamma_0=-psi`. Distinguish spectral derivatives of zeta from argument derivatives of Stieltjes functions.
2. The finite part is the constant term of the integral from epsilon to 1 in the original coordinate x. Delete negative epsilon powers and nonconstant logarithmic powers; no extra subtraction length or finite constant is introduced.
3. Keep the exact integration-by-parts boundary law. For example, the sum of the two first mixed edge products is `-zeta(2)-zeta'(2)`, not zero.
4. Combine both terms of a meromorphic germ before specializing at a removable pole. In the Mellin formulas, `s zeta(s+1)` has value 1 at s=0. Its prefactor cannot simply be set to zero before removing the pole.
5. Keep finite upper endpoints until convergence is proved. This applies to both the tail certificate and the rectangular Gamma primitive. Continued values are not automatically ordinary sums.
6. Preserve the derivatives of the weight `2n+z+w` in every mixed derivative of the shifted kernel. The kernel's rank statement concerns the displayed parameter-dependent weighted kernel; it is not an assertion that an unweighted Gram matrix has rank two.
7. Keep the right-half-plane branches for log Gamma and the slit domain for the polylogarithmic scale. An analytic continuation of a germ is distinct from composing principal branches outside their initial domain.
8. Retain the distinction between coincident and separated singularities. A literal zero-shift substitution into the periodic translated finite part does not establish the coincident law.

No new false source theorem has been established by the targeted audit. The above are status updates and requirements for correct integration. The source corrections already recorded in `chapters/11-stieltjes-source-corrections.tex` should remain attributed to the earlier work.

## 5. Verification and artifact retention

The following counts are from recorded completed work; the article's complete verification manifest may contain additional checks.

| Component | Exact evidence | Numerical evidence and scope |
|---|---|---|
| Tail and shifted kernels | 144 rational bilinear cutoff identities; 72 rational kernel cutoff identities; 3125 divisor strings; symbolic cancellation and rank determinant identities | 21 diagnostics at 50 digits; maximum absolute discrepancy `5.3455294201843913e-51`. The written normal-convergence arguments justify the infinite identities and all mixed derivatives. |
| Mellin/polylogarithm transform | 2002 exact rational/algebraic checks: 91 operator recurrences, 91 Hurwitz-shift annihilations, 455 resonance annihilations, 1365 nonpositive-order beta integrals | 11 direct integer-order or scaled quadratures at 40 digits. These do not constitute numerical verification of arbitrary order derivatives. |
| Stieltjes edge | 81 exact endpoint identities for indices from 0 through 2; four printed-formula comparisons | Five independently integrated finite parts at 55 digits, with one repeated at a second split; maximum recorded error below `1.3e-46`. Four pointwise cross-checks validate the smooth-factor evaluator. No interval certification. |
| Smaller order ten | Nonzero original and retained determinants over F_65537; independent Padé and rational-Bernoulli replay | None needed for the proof. |
| Smaller order twelve | All 11513 required finite cases, independently replayed residue by residue; analytic proof above 11520 | None needed for the proof. |

Retain the complete residue vector, both independent order-twelve implementations, the order-ten independent verifier, source-input hashes, and the actual JSON outputs. Keep source proofs and certificates identifiable; do not replace the full finite certificate with a success flag or a screenshot. The optional sharper coefficient-norm calculation is supplemental: the article's threshold proof uses its stated elementary bound and does not depend on a large unprinted numerical constant.

The combined `verify_all.py` run completed successfully. This status refers to the recorded exact and numerical checks, with the distinction between arithmetic proof certificates and numerical diagnostics preserved.

For scientific transparency, `NUMERICAL_AUDIT.md` records a separate exploratory polylogarithm order-differentiation quadrature that missed its attempted tolerance. That attempt is excluded from the 11 successful quadratures and from any derivative-verification claim. It does not affect the proof, which differentiates a jointly holomorphic identity. Retain the note if that exploratory work is distributed; it need not be treated as a theorem correction.

The exact verification programs and the analytic proofs are complementary. This delivery does not claim proof-assistant formalization, interval-certified quadrature, an exhaustive priority search, or independence of numerical periods.

## 6. Integration review sequence

First preserve the intact archive, source pins, and checksums. Next import the mathematical sections with their definitions and domain conventions, then add their bibliography and cross-references. Update only the specifically identified research-status entries. Run the exact replay programs from a clean extraction and rebuild the unified manuscript; inspect all cross-reference warnings and displayed equations after label conversion. No network lookup should be needed for the recorded finite certificates once their source inputs and manifests accompany the package.

The article is a research continuation relative to the inspected repository and primary literature. The proposed new identities should receive a targeted priority review before a publication-level novelty claim is made; the current wording deliberately states the scope of the search.

# Proposed integration into ProveIt

## Baseline and destination

Baseline commit: `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`.

The article continues `Analysis/Polylogarithms/docs/manuscript` without modifying the remote repository. A suitable independent report location is:

```text
Analysis/Polylogarithms/docs/reports/gaussian-polylogarithms-beyond-parity/
```

The archive's root directory can be moved there as a unit. All executable paths are relative to the installed package, and the article uses relative figure paths. The manuscript source snapshot is not duplicated in full; its revision and file digests are recorded instead. The two small upstream evaluator/matrix modules are included with original paths and checksums because they are inputs to the exact matrix comparison.

## Result-to-manuscript mapping

| Existing material | Proposed change | Proof and artifacts in this package |
|---|---|---|
| `04-shuffle-parity.tex`, `gaussian:conj:S4` | Promote the mixed weight-five identity to a theorem after incorporating the exact proof. | Article Theorem 5.1 and Section 5; `data/s4_exact_certificate.json`; both word replays. |
| `05-signed-kernels.tex`, `signed:conj:rank` | Promote to a theorem; retain the original labels for reference compatibility if desired. Add even-weight ranks and the explicit kernel. | Article Theorem 3.1 and Section 3; `kernel_normal_form.py`; exact rank and normal-form receipts. |
| `05-signed-kernels.tex`, the specified matrix family | Add the all-level generalization as a separate formal coefficient-matrix theorem. | Article Theorem 4.1; `check_general_level.py`. |
| `05-signed-kernels.tex`, `signed:prop:S4-obstruction` | Retain the proposition. Add the all-weight separating family and explain the enlarged system used by the successful proof. | Article Section 3.5 and equation (3.6), followed by Section 5. |
| Gaussian harmonic-sum examples | Add the S2 identity and its classical Li3 specialization. | Article Theorem 5.2; full 25-row certificate, including the printed 23-row double-shuffle table. |
| Signed-kernel analytic continuation | Add global nonvanishing and the real-outer-order kernel extension. | Article Section 7, Theorem 7.1 and Proposition 7.2. |
| Unit-circle angular-zero theorem | Extend to all radii up to one, then add strict parameter order, endpoint comparisons, and the sixth-root sign theorem. | Article Section 8, especially Theorem 8.4. |
| Four-term angular-zero asymptotic | Retain the old four coefficients as a specialization; add the all-order formula, collision rule, and 17-scale table. | Article Theorem 9.1 and Section 9; `all_order_zeros.py`, `zero_coefficients.json`. |
| Euler enclosure constant | Replace the exponent-dependent bound by one; retain the exact rational parameter restrictions in the implementation. | Article Theorem 10.1; `universal_euler.py` and its independent rational self-test. |
| Research agenda | Add normalized-radius monotonicity as a conjecture, with its proved local coefficient and numerical evidence. | Article Proposition 11.1, Conjecture 11.2, and the twelve research questions. |

The article's equation/section numbers are for the delivered version and will change if its content is absorbed into existing chapters. Its stable LaTeX labels are a better basis for cross-reference migration. In particular, use `eq:S4-quotient` for the product-only quotient computation and `rank:thm:all` for the full level-four rank theorem.

## Suggested integration order

1. Add the standalone report and all proof certificates first. Run `python code/run_verification.py` and build `article.tex` in its new location.
2. Add a bibliography entry for the report to the consolidated manuscript.
3. Integrate the rank proof and S4 certificate argument. Promote the two original conjecture environments only when their proofs are present, and update surrounding references that explicitly say “Conjecture.” Existing labels can remain temporarily to avoid broken references.
4. Preserve the original exact obstruction and explain that it is restricted to fixed-weight linear depth-two product rows. The new S4 proof uses all depths and octahedral transformations, so the two results are compatible.
5. Integrate the analytic extensions with their exact scopes. In particular, real-order existence is proved; full real-order parameter motion is not.
6. Apply the small textual patch below, then reconcile the editorial ledger and the affected chapter introductions and conclusions.

No publication, merge, or repository write is performed by this deliverable.

## Small correction patch

`patches/manuscript_text_corrections.patch` contains:

- Removal of a duplicated “endpoint signs” phrase in `09-zero-geometry.tex`.
- `P_1` to `Q_1` in the sentence identifying the root `-gamma` in the proof labelled `half:zero:first`.
- “Equivalently” to “Consequently” following the two conjectured ranks, together with the corresponding rank-nullity explanation. The rank difference determines the dimension of Gaussian-supported consequences; it does not independently determine both ranks.

From the repository root, first check against the current version:

```bash
git apply --check path/to/manuscript_text_corrections.patch
```

The patch was checked successfully against an isolated copy of the pinned revision. Later upstream changes may require a small contextual adjustment. The patch intentionally does not promote theorem status on its own: that change should be made together with integration of the proofs.

The old zero-profile figure caption also contains earlier notation. It should be checked against its plotted source data before editing; the patch makes no unverified change to that figure.

## Preservation requirements

Keep both independent certificate replays, the rational coefficient JSON files, the degree-one regularization argument, and the explicit convention converting Li words to H words. These are the essential interfaces for auditing signs and endpoint behavior. The modular discovery matrix is not needed for acceptance and is not bundled as a proof dependency.

Keep the distinction between:

- a formal relation-module obstruction and arithmetic independence;
- an exact word certificate and a numerical residual enclosure;
- an all-order finite asymptotic theorem and convergence of an infinite series;
- integer-order parameter-motion theorems and the separately proved real-order existence/nonvanishing results;
- numerical plots and rational endpoint certificates.

The basis vectors called integer or integral in the rank discussion are a rational basis with integer coordinates. No claim that they form a saturated basis of the integral kernel lattice is made.


# Proposed integration and research-status updates

Repository checkpoint: `e3d7ec5d3f9be259c1f91edaea4389f4e79b5b03`.

These are proposed editorial changes for integration of *Boundary Contacts and Logarithmic Spectral Integrals*. The original reports should remain intact as historical source evidence. No repository source was changed, and no remote action was taken. The accompanying `data/source_manifest.json` identifies the seven incoming archives and the directly inspected manuscript and preserved sources by SHA-256. A hash records source identity; it is not a certificate that every assertion in a source has been audited.

## 1. Complete the independent bilinear contact question

**Source:** `docs/incoming/ProveIt_Bilinear_Tails_and_Determinants_2026-10-11.zip`, member `ProveIt_Bilinear_Tails_and_Determinants_2026-10-11/sections/10_research_questions.tex`, question headed **Every bilinear contact hyperplane**.

**Proposed status:** Completed in the specified Gamma-normalized alternating-tail family, for independent complex orders and independently shifted arguments with Re a > 0 and Re b > 0. The new finite coefficient formulas give the symmetric and antisymmetric contacts on every hyperplane `p + q = -2m`, every independent order derivative, and every fixed translation of the cutoff. The contact degree is at most `m`; the sharp leading-degree formulas describe when the threshold is attained. Normally convergent subtractions give ordinary-series representatives as well as cutoff finite parts.

**Article mapping:** `ct:ck`, `ct:dk`, `ct:contacts`, `ct:logjets`, `ct:translate`, `ct:top`, `ct:normal`, `ct:resonantconvergence`. The explicit ordinary evaluations involving pi and log 2 are `ct:exampleplus` and `ct:exampleminus`.

**Attribution to retain:** The finite bilinear endpoint law, its Gamma normalization, and the symmetric first contact `1/2` at `p + q = 0` are inherited. The source's diagonal contact theory is also inherited. The new result supplies the independent bivariate coefficients and transverse derivatives requested by the source question. It does not solve the independent outer-weight ordinary-Hurwitz-tail problem, the classification of more colors, or the general higher-product certificate problem.

**Suggested ledger sentence:**

> The independent bilinear contact problem is completed by finite bivariate coefficient formulas at every resonance, all mixed order jets, the exact fixed-cutoff translation law, sharp degree bounds, and normally convergent ordinary representatives. The finite Gamma-normalized endpoint identity and the earlier diagonal contact calculus retain their original attribution.

## 2. Advance the higher quadratic and many-mass questions with precise scope

**Sources:**

- `ProveIt_Higher_Quadratic_Jets_2026-10-11.zip`, `sections/10-research.tex`, item 3, **Higher-order two-mass and many-mass interactions**.
- `ProveIt_Higher_Spectral_Defects_2026-10-11.zip`, `article.tex`, research item 3, **Higher-order multi-mass connected terms**.

**Proposed status:** The scalar all-order representation and connected logarithmic-product portions are completed. For a positive one-sided lattice and finitely many positive quadratic masses, every scalar spectral derivative at zero is represented by one ordinary real integral with an explicit logarithmic density and a digamma resolvent. The representation includes the complete scalar third jet for two masses. Connected products of arbitrary order have a compactly supported density; its first moments vanish exactly. Repeated masses, divided resolvents, explicit polynomial subtractions, the critical odd weight, and the fixed-regulator extension to any polynomial weight are provided. The number of integration variables remains one as the number of masses and the derivative order increase.

**Article mapping:** `sp:master`, `sp:master-formula`, `sp:explicit-densities`, `sp:mass-derivatives`, `sp:repeated-mass-derivatives`, `sp:compact-density`, `sp:compact-moments`, `sp:coincident-density`, `sp:ordinary-connected`, `sp:critical-weight`, `sp:weighted-compact`. The `da:` section supplies the coefficient and arithmetic bridges, including the confluent harmonic expansion and the beta/polylogarithmic transform.

**Further extension to even weights and negative spectral points:** The `ng:` section subtracts the finite polynomial-logarithmic asymptotic part before forming the cut density. It gives a single ordinary digamma integral for every even polynomial weight and every derivative order. Taking the weight to be the product of all quadratic factors raised to an integer power gives every jet at every nonpositive integer spectral point, with an explicit finite Hurwitz-derivative baseline. The explicit third jet at the first negative point and a two-mass second jet have independent numerical checks against both ordinary remainder sums and binomial spectral continuation. Relevant labels are `ng:finite-continuation`, `ng:ordinary-series`, `ng:master`, `ng:negative-integers`, and `ng:cubic-negative-jet`.

**Scope to keep open:** An ordinary integral representation is not a finite special-value reduction to a smaller declared alphabet. The negative-point extension completes the representation in the stated one-variable digamma-integral class; it does not supply the separate terminating Bessel-order recurrence or finite polylogarithmic-kernel reduction requested in the predecessor's higher Fourier-jet programme. Finite polylogarithmic closure at all special parameters and any larger independently weighted multivariable resonance classification require separate theorems. The article does not claim to resolve every item in either predecessor's research programme.

**Suggested ledger sentence:**

> The many-mass higher-jet programme now has a one-variable digamma integral for every scalar zero-point jet and a compact one-variable density for every connected logarithmic product, with exact moments, polynomial-weight subtractions, and confluent formulas. Finite asymptotic subtraction further gives one ordinary digamma integral for every even polynomial weight and every jet at each nonpositive integer spectral point. These complete the stated integral-representation and connected-product targets. Finite reductions of the resulting integrals to prescribed smaller special-function alphabets and the separate higher Fourier-kernel programme remain distinct questions.

## 3. Attribute the local spectral hierarchy to the preserved continuation

**Preserved source:** `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/arithmetic-spectral-jets/sections/03-local.tex`.

**Source labels:** `asj:thm:polynomial`, `asj:thm:top`, `asj:thm:all-differences`, `asj:eq:scaling`.

This source already provides normalized Laurent-jet polynomiality, the finite principal-part correction, top polarization, all higher finite local differences, and the normalization/scaling law. The article's polynomial-weight correction is a specialization with its normalization checked directly from the resonant Hurwitz factor. It must not be advertised as a newly discovered general interaction hierarchy or regularized-trace principle.

**Article mapping:** `sp:inherited-local-correction`, `sp:inherited-correction`, with the fixed-number-of-factors convention at `sp:fixed-N-differences`.

The independent use of the words “degree” and “interaction” must remain clear: the bilinear contact degree concerns the orders `p,q`, while the spectral interaction degree concerns replacement of labeled masses with their total number held fixed. Deleting a factor changes the normalization and is not the same finite-difference operation.

## 4. Reconcile two stale Tail Kernels questions

**Source:** `docs/incoming/ProveIt_Tail_Kernels_and_Boundary_Products_2026-10-11.zip`, member `ProveIt_Tail_Kernels_and_Boundary_Products_2026-10-11/sections/08_audit_and_research.tex`.

### R9: Cubic Stieltjes products with independent indices

The finite holomorphic-germ target is already answered in the preserved source

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/coincident-directional-zeta/sections/02_cubic.tex`.

In particular, `cub:general-completion` and `cub:all-moments` supply the local counterterm and all-index framework, while `cub:global` and `cub:Lr` give the finite cubic Tornheim representation. This includes the coefficient-germ level of the displayed target involving `gamma_1(x)^2 gamma_0'(x)`. This is an inherited solution, not a new theorem of the present article.

**Suggested replacement status:**

> The independent-index cubic finite-part germ and its local counterterms are already available in the preserved coincident-directional-zeta continuation, with a finite Tornheim-zeta coefficient representation. Further reduction of these coefficients to specified depth-one constants or another smaller arithmetic alphabet remains a distinct research question.

The word “finite” here describes a finite kernel/coefficient formula. It does not assert that the Tornheim derivatives reduce to ordinary zeta values and their derivatives.

### R7: Continued alternating-square law at nonpositive orders

The diagonal problem, including all spectral derivatives and translated cutoffs, is already answered by `ProveIt_Bilinear_Tails_and_Determinants_2026-10-11.zip`, member `ProveIt_Bilinear_Tails_and_Determinants_2026-10-11/sections/04_cutoff_jets.tex`.

**Source labels:** `cut:normal`, `cut:contacts`, `cut:translation`; the complete formulas are `cut:contacteq` and `cut:translationeq`. The order-zero discrepancy between the continued value `1/4` and the zero pointwise sum is explicitly recovered there.

**Suggested replacement status:**

> The diagonal alternating-square continuation and every nonpositive-order cutoff jet, including translated-cutoff contacts, were completed in Bilinear Tails and Determinants. The present article extends the contact calculation to the independent two-order Gamma-normalized family; the inherited diagonal result remains the mandatory specialization check.

## 5. Preserve the remaining reconstruction questions

The general determinant/reconstruction problem for all unequal even orders remains open. The full fixed-gap-six family, conventionally `b = a + 3` in the centered formal coordinates, also remains open. Completed fixed smaller-order families and exact examples are inherited from the supplied reconstruction reports and do not settle either unrestricted question. The present article supplies no new determinant nonvanishing theorem and no arithmetic-independence claim for evaluated zeta values.

No closure should be recorded for the full reconstruction question or the full gap-six conjecture on the strength of the contact or logarithmic-density results.

## 6. Apply the single definite source correction

**File:** `Analysis/Polylogarithms/docs/manuscript/chapters/07-digamma-power-moments.tex`.

**Equation label:** `dgp:eq:a5`.

Replace the literal final numerator term `+24\zeta\alpha_5` by `+24\zeta_5`. This is the coefficient of the fifth zeta value in the degree-five reciprocal-Gamma coefficient; it follows immediately by expanding the displayed logarithm of `1/Gamma(1+u)`.

The patch is `integration/corrections.patch`. `git apply --check` succeeded against the pinned checkout; the patch has not been applied. `data/correction_patch_validation.json` records the command outcome, patch hash, and unchanged-source check. No other source typo or mathematical correction is included in the patch.

## 7. Label and evidence map

| Article prefix | Content to integrate | Main dependency/status |
|---|---|---|
| `ct:` | Independent bilinear contacts, mixed jets, cutoff translations, convergent subtractions, ordinary examples | New completion of the explicitly open independent contact target; finite endpoint law inherited |
| `sj:` | Generalized Stieltjes boundary series, all independent order jets, argument derivatives, and harmonic reductions | Explicit consequences of the completed contact algebra; classical special-function conversion formulas attributed |
| `sp:` | Full scalar spectral integrals, compact connected densities, weighted resolvents and coincident limits | New explicit all-order representations; local principal-part hierarchy inherited |
| `ng:` | Every even polynomial weight and all jets at nonpositive integer spectral points, with finite Hurwitz baselines and one ordinary digamma integral | Explicit extension of the cut-density representation; does not establish finite special-value closure or the separate higher Fourier-kernel recurrence |
| `da:` | Logarithmic-density arithmetic, harmonic coefficients, beta moments and polylogarithmic transforms | Derived bridge to classical Gamma, harmonic, Stirling and height-one alphabets; no new priority claim for classical constants |

Mathematical proofs determine the all-order claims. Exact finite coefficient checks and independent high-precision diagnostics support implementation and transcription. Decimal agreement is not an interval certificate, a proof of arithmetic independence, or a replacement for the analytic continuation and convergence arguments. Historical source verification receipts are not represented as fresh replays in this delivery.

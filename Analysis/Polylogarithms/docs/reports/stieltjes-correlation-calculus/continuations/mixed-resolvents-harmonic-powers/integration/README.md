# Integration guide

## Article and source baseline

**Mixed Resolvent Products, Higher Digamma Powers, and Stieltjes Collisions: Exact identities and normalized finite parts** continues the Hurwitz–Stieltjes and harmonic-identity material in ProveIt.

The comparison baseline is commit **9035bb0eaaf70f3398711b489733093dcc52e946**, including the manuscript and all 17 incoming ZIP archives present at that revision. “New” in this guide means new relative to that inspected corpus. It does not claim worldwide priority for classical consequences or replace a comprehensive literature review.

- [Article PDF](../Mixed_Resolvents_Harmonic_Powers_Stieltjes_Collisions.pdf)
- [Modular article source](../article.tex)
- [Claim ledger](CLAIM_LEDGER.csv)
- [Internal independent review record](INDEPENDENT_REVIEW.txt)
- [Independent collision review record](COLLISION_REVIEW.txt)
- [Build, verification, and layout record](VALIDATION.json)
- [Pinned manuscript](https://github.com/VladimirReshetnikov/ProveIt/tree/9035bb0eaaf70f3398711b489733093dcc52e946/Analysis/Polylogarithms/docs/manuscript)
- [Pinned incoming directory](https://github.com/VladimirReshetnikov/ProveIt/tree/9035bb0eaaf70f3398711b489733093dcc52e946/docs/incoming)

These files propose incorporation. **No change has been applied to the ProveIt repository.** The package is an independent article and verification bundle, not a patch that changes existing theorem or conjecture statuses automatically.

## Main additions

### Independent complex powers of several resolvents

Section **mr:section** gives the full Fourier spectrum, the Hurwitz transform, and the complete endpoint normalization of any finite product of nonreal cotangent resolvents. Repeated parameters are allowed. Parameters may occupy either or both half-planes.

The principal incorporation units are **mr:fourier**, **mr:hurwitz**, and **mr:completion**. Their ordinary-integral domain, branch normalization, and local completion should remain attached to the formulas. For mixed orientations, the signed sum of the exponents matters in addition to their total. The phase residue **mr:mixedresidue** and the exact path examples **mr:pathlimit**–**mr:fixedmean** show why an uncompleted continuation along an exponent path need not give the finite part in the original integration coordinate.

These results answer the Fourier/beta transformation and resonance-completion parts of **Quartic Question 10**. A smaller named-function expression for every exponent pattern, general arithmetic reductions at algebraic disk coordinates, and real-axis boundary limits remain separate questions.

Useful exact consequences include the log-Gamma transform **mr:loggamma**, the Gamma specialization **mr:specialmean**, the finite-part logarithmic family **mr:negativeLog**, and the polynomial moments **mr:expmean**. Their classical beta and Gamma ingredients retain the article’s original citations.

### Finite polylogarithmic mixed logarithmic transforms

Section **ml:section** reduces the transform of two oppositely oriented centered logarithmic resolvents to depth-two multiple polylogarithms. The theorem **ml:allStieltjes** covers every Stieltjes index and every ordinary argument-derivative order, including the full local finite-part subtraction.

Keep the strict decreasing-index convention **ml:MPL** and the complete limiting definition **ml:T11** with this result. The expression at the color pair (1,1) is a convergent combined value in its initial domain; the separate divergent factors are not to be specialized independently.

The section also gives the ordinary dilogarithmic covariance, the three-logarithm formula **ml:triple**, the exact harmonic-Laurent identity **ml:specialStieltjes**, the special-point Gamma moment generator, and a two-parameter primitive **ml:doubleprimitive**. The Gamma generator and its cumulants are explicit classical specializations, not claims of a new beta integral.

### Every digamma power and the explicit fifth bridge

Sections **hp:sec:all** and **hp:sec:fifth** give a terminating reduction for every positive integer power of the digamma function, a primitive with fixed additive constant, and the complete fifth finite-part integral.

The proof units **hp:ML**, **hp:regularization**, and **hp:allpowers** belong together. Matching principal parts alone does not fix the entire remainder; the contour argument does. Likewise, the finite harmonic identity and its asymptotic constant are separate steps. The strict quasi-shuffle recurrence first acts on finite sums and only then replaces convergent terminal words by their limits.

The theorem **hp:fifth** answers **Quartic Question 1** and supplies the explicit fifth case requested in **Barnes Question F3**. The all-power theorem answers the finite-reduction aspect of F3 in a specified output class: convergent multiple zeta values and first Laurent coefficients of strict moving-order multiple zeta functions. It does not prove a smallest arithmetic basis.

The fifth formula retains the explicitly normalized depth-four coefficient phi and the convergent depth-two derivative combination chi_4. Corollary **hp:cancellation** removes the inherited eta and theta coordinates from a specific fifth-degree polynomial. Because chi_4 remains, this is partial progress on **Quartic Question 2**, not a proof of universal reduction to one highest-depth coordinate.

### Higher-index Stieltjes collisions

Section **gcx:section** constructs a finite Hermite counterterm for arbitrary Stieltjes indices and ordinary argument derivatives, with a periodic smooth weight that is analytic near the collision point. The theorem **gcx:main** proves that the fully subtracted total-collision limit equals the directly merged coordinate finite part. No comparability of gaps is required.

This answers the existence and explicit-counterterm part of the Higher Reflection report’s **“Higher Stieltjes geometric collisions”** question. It also answers the analytic-weight part of its **“Integer-frequency grids and Fourier weights”** question at common unit frequency. The theorem uses a finite Hermite construction and a fixed-contour argument; its statement is a continuity result after subtraction.

The counterterms reduce to finite generalized polylogarithms of the stated weight. At total Stieltjes index one, the explicit dilogarithm table **gcx:U-table** suffices. The three cubic placements **gcx:three-T** have different uncompleted order-zero constants, evaluated in **gcx:CT-values**. Their difference **gcx:CT-difference** eliminates the common global merged constant exactly.

Do not strengthen this result to analyticity of the remainder at positive Stieltjes indices, arbitrary integer-frequency grids, or associativity of independently chosen successive merger prescriptions. Those questions remain open. Formula **gcx:Q-ordinary** supplies a convergent representation of the merged constant Q, not an evaluation of Q in a smaller arithmetic algebra.

## Reconcile inherited results before changing status records

The archive names below identify sources at the pinned revision. The CSV uses the short names in its source fields.

| Short name | Archive and relevant members | Required treatment |
|---|---|---|
| Quartic | ProveIt_Quartic_Tails_Resolvents_2026-10-11.zip; sections/quartic_bridge.tex, sections/complex_powers.tex, sections/mixed_even_tails.tex, sections/research_questions.tex | Credit the existing quartic bridge, single-resolvent completion, and pure two-tail evaluations. |
| Barnes | ProveIt_Barnes_Resolvents_and_Harmonic_Identities_2026-10-11.zip; sections/05_quartic_harmonic.tex and sections/07_audit_research.tex | Mark F5 as answered by Quartic, not by this article. Add the present results to F3 with their retained-coordinate scope. |
| Cubic | ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip; sections/02_cubic_harmonic.tex | Preserve the earlier cubic digamma bridge and its strict Laurent convention. |
| Higher Reflection | ProveIt_Higher_Reflection_Identities_2026-10-11.zip; sections/04_collision.tex and sections/06_audit_research.tex | Preserve the index-zero collision and derivative theorems. Update only the higher-index limit and common-unit-frequency weight portions. |
| Harmonic Parity | ProveIt_Harmonic_Parity_and_Resolvent_Identities_2026-10-11.zip; sections/07_research.tex | Its earlier pure-pair even-tail evaluation question was already answered by Quartic. Additional harmonic factors and further tails remain separate. |
| Exact Resonant | ProveIt_Exact_Resonant_Identities_2026-10-11.zip; source audit, research-status material, and Gaussian/Cayley certificates | Retain the exact scope of every formal relation-space obstruction; none proves arithmetic independence or settles the Gaussian period conjectures. |

In particular:

- **Barnes F5, nonpositive single-kernel resonances:** already proved in Quartic. The present extension concerns independently varying exponents and mixed orientations.
- **Cubic and quartic digamma powers:** already proved. The new additions start with the uniform construction and explicit fifth power.
- **Pure products of two even harmonic tails:** already evaluated in Quartic. This package does not claim that result again.
- **Stieltjes-index-zero geometric collisions and ordinary derivatives:** already proved in Higher Reflection. The present extension adds arbitrary Stieltjes indices and analytic local weights.
- **All-degree formal Tornheim relation spaces:** prior work. Their specified formal dimensions are not arithmetic independence statements.
- **Frozen S6 and revised S8:** remain conjectural. The rejected earlier S8 coefficient vector remains a different, already rejected claim. This package supplies neither a proof nor a counterexample for the current targets.

The focused audit found no additional false theorem in the established source portions reviewed. The new exact counterexamples reject unsupported extrapolations concerning uncompleted parameter limits and collision constants. They do not invalidate the earlier single-resolvent or index-zero collision theorems.

## Recommended placement in Volume III

The canonical driver is **volumes/volume-3-hurwitz-stieltjes.tex**, titled *Hurwitz Jets, Stieltjes Calculus and Gamma Correlations*. It shares chapter sources with the unified manuscript. Integrate through those shared chapter sources, rather than inserting independent copies into the volume driver and the unified driver.

The file-name numbers do not equal the displayed chapter numbers. Use the stable labels and source paths below.

| Incorporation unit | Suggested shared source neighborhood | Labels to retain |
|---|---|---|
| Conventions and full-amplitude completion | The common Hurwitz-jet and finite-part foundations in chapters/07-integration.tex; cross-reference the existing Stieltjes convention instead of duplicating it | scope:completionlemma; scope:monomial; scope:resonantmonomial |
| Several resolvents and their logarithmic transforms | A new shared section after the existing single-resolvent and complex-power material, when the Quartic dependency is incorporated; connect to ch:07-integration and stieltjes:thm:transform | mr:section; mr:fourier; mr:hurwitz; mr:completion; ml:section; ml:allStieltjes |
| All digamma powers and the fifth bridge | New shared sections after the cubic/quartic harmonic bridges, with a cross-reference to chapters/07-harmonic-gamma-coefficients.tex, label ghharm:sec:main | hp:sec:all; hp:ML; hp:primitive; hp:allpowers; hp:sec:fifth; hp:fifth; hp:cancellation |
| Geometric collision theorem and examples | Following the convolution/collision foundations near chapters/07-stieltjes-convolution-foundation.tex and chapters/07-shifted-stieltjes-correlations.tex; add a cross-reference from chapters/08-stieltjes-contact-products.tex | gcx:section; gcx:main; gcx:regularity; gcx:one-log; gcx:three-T; gcx:CT-values |
| Audit and research status | Consolidated status and research records; preserve original source attribution and cross-volume Gaussian references | audit:section; the exact result labels recorded in the CSV |
| Verification and provenance | The manuscript verification/provenance structure, with relative paths updated during incorporation | verification:section; verification scripts and recorded JSON files |

The existing contact-product chapter treats derivatives of periodic distributions. The new collision theorem uses ordinary argument derivatives on open intervals and right-hand coordinate finite parts. Preserve that distinction when cross-linking the chapters.

The Gaussian status discussion belongs primarily with the existing Volume I records, including chapters/04-depth.tex, chapters/04-S8-candidate.tex, and the associated certification/obstruction material. A Volume III cross-reference should not introduce a second definition of the frozen targets.

During editorial incorporation, preserve the theorem/equation label namespaces, merge bibliography entries by source identity, reconcile macros with the collective preamble, and record the added sources in the source inventory and editorial ledger. The standalone article preamble and title page are build wrappers, not shared chapter content. Rebuild the unified manuscript and all affected volumes using the repository’s existing workflow so that cross-volume destinations remain consistent.

## Ledger and evidence conventions

Each row of CLAIM_LEDGER.csv identifies a claim, its actual article labels, the precise source question or dependency, its status relative to the pinned corpus, and a proposed destination. Semicolons separate multiple labels within a field.

The statuses distinguish analytic results proved here, consequences with classical inputs, exact counterexamples to extrapolations, inherited results, partial resolutions, open questions, and verification evidence. **“Proved here” records the analytic or finite algebraic proof in the article; it does not mean formalized in a proof assistant.**

The verification code checks finite identities and independently compares analytic representations. The JSON values record floating-point diagnostics at stated working precisions. They are not interval certificates. In collision checks, C−T−Q at positive separation is a remainder approaching zero, not an equality error that should vanish at that separation.

INDEPENDENT_REVIEW.txt records an additional internal mathematical cross-check of the resolvent, mixed-logarithm, and higher-digamma sections. COLLISION_REVIEW.txt records the separate independent check of the collision theorem and its examples. These are internal checks, not external peer-review reports, whole-corpus audits, or proof-assistant certificates.

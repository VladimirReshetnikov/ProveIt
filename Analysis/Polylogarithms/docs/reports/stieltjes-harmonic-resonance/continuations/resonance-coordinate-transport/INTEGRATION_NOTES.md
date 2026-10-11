# Integration notes: resonances, local coordinates and unequal frequencies

## Baseline and audit scope

This package continues [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt) at commit **`445f754610e1377939235794de84ed9075fc09f5`**, using the requested directories `Analysis/Polylogarithms/docs/manuscript` and `docs/incoming`. All references below concern that pinned snapshot. The package proposes manuscript additions; it does not modify the repository.

The review covered relevant manuscript passages and the mathematical text of the Gauss–Hurwitz, Mellin–Dilation, Nested Harmonic Jets and Stieltjes–Harmonic incoming reports. The fifth report, Polylogarithm–Stieltjes Continuation, was checked through its introduction and audit/research discussion to reconcile scope and proof status. This is a **targeted audit**. It does not certify every theorem of the source book or replay every program in the incoming archives. No new false theorem was found in the selected claims examined. The PSLQ wording correction discussed below was already proposed in the Gauss–Hurwitz report.

The machine-readable inventory in `provenance/source_manifest.json` distinguishes all 76 retrieved manuscript text files from the passages inspected for this work. It records exact repository paths, Git blob identifiers, source SHA-256 hashes, archive member paths, and the three research-question crosswalks. The manuscript text transport appended one terminal LF byte to each local copy; removing exactly that byte reproduced all 76 pinned Git blob identifiers. Archive hashes were verified against the original archive bytes without text normalization. No original source archive or copied manuscript tree is included in this deliverable.

## Incoming source inventory

The archive paths are `docs/incoming/` followed by the exact filename in this table. Their identities are pinned to the commit above. The corresponding SHA-256 values and byte lengths are in the manifest.

| Short name | Exact source filename | Verified Git blob SHA-1 |
|---|---|---|
| GH | `ProveIt_Gauss_Hurwitz_2026-10-10.zip` | `069b39cdc5a241c3e016f1780fd481dd3069d63a` |
| MD | `ProveIt_Mellin_Dilation_2026-10-10.zip` | `246d0422f9ad599fb487f5210cedf41168b78a1d` |
| NH | `ProveIt_Nested_Harmonic_Jets_2026-10-10.zip` | `28354d64b9d779ce7c5d42b166293bae1c974e26` |
| PC | `ProveIt_Polylogarithm_Stieltjes_Continuation_2026-10-10.zip` | `2b19b137342f68561fe7bca55da16caa2291baf1` |
| SH | `ProveIt_Stieltjes_Harmonic_Identities_2026-10-10.zip` | `caf56a1906c3cfc46fd61cbad19af9aa174d35eb` |

Except for PC, member paths start with the archive filename without `.zip`. PC instead uses `polylogarithm_stieltjes_continuation/`. The manifest records every inspected TeX member under its exact internal name. NH is a single `article.tex`; GH, MD and SH use modular `sections/*.tex`. The two PC members inspected are `article/00_introduction.tex` and `article/06_audit_and_questions.tex`.

## Research questions and the additions that answer them

### 1. A complete resonant Dougall family

**Source target.** GH, `sections/09-research.tex`, paragraph 1, “Classify summation families admitting complete jet closure,” proposes a fixed Dougall-type summation with one excess parameter and an explicit residue polynomial as its first concrete target. SH, `sections/further_research.tex`, “Negative-balance identities and other summation theorems,” asks for a coherent further summation family with a complete jet theorem.

**Addition.** `sections/01_dougall.tex` and `sections/02_dougall_jets.tex` supply centered asymptotic coefficients, explicit pole residues, every nonpositive-integer resonance, and every spectral Taylor coefficient for the stated very-well-poised family. Reciprocal-Gamma zeros are retained before differentiation. The quartic central-binomial specialization gives explicit harmonic identities at all resonances. `sections/03_polylog_primitives.tex` gives a weighted primitive and finite rational-shift conversion to colored polylogarithms and their order derivatives.

Preserve labels `dg:master`, `dg:residues`, `dg:closed`, `dg:half`, `dg:alljets`, `dg:closure`, `dg:quarticall`, `dp:primitive`, and `dp:filterjets`. The fixed Dougall target is answered. The broad classification of summation submanifolds, general multivariate resonance, and unrelated mixed harmonic Stieltjes coefficients remain open.

Dougall’s summation, Gamma-ratio asymptotics and root-of-unity filters are classical. The article credits Bühring’s zero-excess and quartic-binomial antecedents; the first quartic row is recovered, rather than presented as a new evaluation. The claimed extension is the particular centered subtraction, uniform resonance law and complete spectral coefficient calculus. No global priority claim is made for every specialization.

### 2. Nonlinear coordinate corrections

**Source targets.** MD, `sections/06-audit-research.tex`, proposed research programme item 3, “Nonlinear changes of local coordinate”; SH, `sections/further_research.tex`, the nonlinear-coordinate paragraph of “Collision identities and nonlinear coordinate changes.” Both request a finite delta-derivative law for an analytic map with positive linear coefficient, recovery of the affine result, and compatibility with composition.

**Addition.** `sections/04_nonlinear.tex` proves the finite local residue law for logarithmic meromorphic germs, specializes it to every `gamma_n^(r)`, and derives its composition rule. Its coefficients depend only on a finite coordinate jet. A map tangent to the identity has zero correction whenever `n >= 2r`, with a sharp order filtration below that threshold. Explicit low-order examples, polygamma consequences and a local coincident-product formula are included. Preserve labels `nc:universal`, `nc:composition`, `nc:Stieltjes`, `nc:rigidity`, and `nc:coincident`.

Three conventions are essential during integration. Pullback is the scalar-distribution pullback with the inverse Jacobian in the test-function pairing. The correction for the finite part of an argument derivative differs from the correction for the distributional derivative of the periodic finite part: the article uses `alpha(L) = b(L) - b(0)` for the former. The composition law acts on the transformed singular germ, as explicitly stated in `nc:composition`; deleting that transformed input loses terms. The derivative-contact comparison uses the common smooth periodic completion at the endpoint.

This answers the nonlinear-coordinate question. The separate question comparing a limit of separated singularities, a coincident-product finite part, and a joint spectral regular coefficient remains open. The local coincident-product example is not asserted to settle that comparison.

### 3. Three unequal integer frequencies

**Source targets.** SH, `sections/further_research.tex`, “Three unequal integer frequencies,” asks for the three-frequency spectral kernel with the local normalization included, first for disjoint singular grids. MD’s programme item 4, “Three translated or dilated factors,” is the earlier related question. SH had already supplied the equal-frequency translated triple formula.

**Addition.** `sections/05_transport.tex` proves an all-index finite transport formula for three positive integer frequencies with pairwise disjoint singular grids. A finite Hurwitz multiplication identity reduces it to the inherited equal-frequency triple kernels, explicit bilinear Stieltjes terms, and a scalar term. The fixed endpoint coordinate is accounted for before coefficient extraction. `sections/06_correlations.tex` adds an independent finite filter for integer-weighted Tornheim sums, convergent centered log-Gamma correlations, and an explicit digamma example.

Preserve labels `tr:finite-transport`, `tr:pair-closure`, `tr:T-negative`, `tr:unit-spectral`, `tr:spectral-lift`, `tc:root-filter`, and `tc:Gamma-triple`. Ordinary colored Tornheim kernels suffice for this integer-frequency problem. Preserve the disjoint-grid hypothesis in the singular Stieltjes product theorem; the ordinary log-Gamma integral has its own stated domain. The finite representation does not prove period independence or a minimal number of coordinates.

## Proposed manuscript placement

The destinations below are suggested new fragments, not existing repository files. Locate insertions by source labels, since printed chapter numbers can change.

| Proposed addition | Existing source anchor | Editorial action |
|---|---|---|
| `chapters/07-dougall-resonance.tex`, from package sections 01–03 | `chapters/07-integration.tex`, “The common Hurwitz-jet calculus” (`stieltjes:sec:intro`) and “Zeta jets and the conversion dictionary” (`stieltjes:sec:jets`) | Place beside the GH subtraction calculus when that incoming report is integrated. Keep the all-order definitions with the formulas. Cross-reference the harmonic-number material and the finite Fourier dictionary. |
| `chapters/08-finite-part-coordinates.tex`, from section 04 | `chapters/08-differentiation.tex`, “The uniform master identity” (`tower:sec:master`, `tower:thm:master`) | Add after the pointwise derivative discussion and the incoming affine/contact conventions. Retain the distinction between pointwise derivatives and distributional derivatives. |
| `chapters/07-unequal-frequency-correlations.tex`, from sections 05–06 | `chapters/07-integration.tex`, with the incoming SH trilinear section; related existing fragment `chapters/07-loggamma-moments.tex` (`gaussian:sec:gamma`, `gaussian:thm:cubic-compact`) | Keep the equal-frequency formula and new finite transport together. Cross-reference the existing cubic Tornheim representation and `chapters/07-tornheim-evaluation.tex`; do not replace their independent evaluation record. |
| Rational colored specializations | `chapters/08-conductor-jets.tex`, “Cyclotomic polylogarithm traces” (`jets:sec:traces`, `jets:eq:polylog-Hurwitz-DFT`) | Add cross-references to the finite polylogarithm and frequency filters. These complement the existing conductor descent and do not replace it. |

Merge theorem environments, notation and bibliography keys with the book’s conventions. In particular, retain factorials distinguishing Taylor coefficients from derivatives and retain the combined convergent subtraction before splitting any displayed sum. The supplied tests check finite coefficient identities and independent numerical representations; they are not a proof-assistant development or an inherited-book validation run.

## Inherited wording correction, verified at this baseline

At `chapters/07-integration.tex`, label `integral:neg:psim2`, the current text says that “Basis atoms must be” rationally independent when discussing PSLQ returning a pre-existing relation. GH `sections/08-audit.tex`, “A narrowly scoped manuscript wording correction,” already identifies the overstatement. A dependency with zero target coefficient can make that output uninformative for the target; dependence itself is allowed input to an integer-relation algorithm.

The GH replacement remains appropriate for the verified current wording:

> Known rational dependencies among the supplied constants should be removed or modeled explicitly. Otherwise PSLQ may return a pre-existing relation with zero target coefficient instead of an evaluation of the target.

Credit this as an inherited editorial correction. It changes no special-function identity. No source patch is applied by this package.

## Proof statuses that must be preserved

| Source claim | Exact current source and label | Status after this package |
|---|---|---|
| Mixed Gaussian `S4` reduction | `chapters/04-S4-proof.tex`, `s4proof:thm:s4` | Already proved; unchanged. |
| Current `S6` candidate | `chapters/04-cyclotomic-quotients.tex`, `cycloquot:conj:S6` | **Conjectural.** |
| Two `S6` coordinate baskets | Same file, `s6change:prop:coordinates` | Their equivalence is proved; equality of either residual to zero is unproved. |
| Current `S8` candidate | `chapters/04-S8-candidate.tex`, `s8new:conj:S8` | **Conjectural.** |
| Precisely frozen older `S8` vector | `chapters/10-discovery.tex`, `research:prop:S8-rejected` | Already rigorously rejected; distinct from the current candidate. |

The new resonance, coordinate and transport identities provide additional exact tools. They supply no missing analytic certificate for the current `S6` or `S8` residuals. Future integration should preserve both the successful exact identities and the limits of the research questions actually answered here.

# Source and proof audit

Date: 23 September 2026.

## Proof status

The article provides mathematical proofs of its main coding, uniformity-gap, initial-core, birthday-controlled denominator, and restricted arithmetic results. No new Lean code was produced; no Lean project build was run. The article is a research manuscript, not a certificate of formal verification or bibliographic priority.

The dependency-sensitive steps are particularly explicit:

- Ambient definability uses external satisfaction for a transitive set model, never an implicit internal truth predicate.
- Elementary exponential closure uses o-minimal definable selection, applied formula by formula.
- The first omitted ordinal is an externally chosen minimum; its epsilon property is proved from finite Cantor normal form.
- Elementarity of the intersection defining the core uses common definable selectors. Arbitrary intersections of elementary substructures are not presumed elementary.
- Fraction recovery inside the core uses classical birthday bounds and the explicit denominator omega^(birthday(x)+1). It is not inferred from the integer-part property alone.
- Pointwise definability of normal-form entries is distinguished from definability of the complete graph.
- Coding an arbitrary set in the pointwise-definability converse uses an existential choice of well-founded relation code, not a nonexistent canonical well-ordering of every set.
- The finite quotient proof uses additive divisibility. The full-class theorem about all set-sized target rings is not transferred to an externally countable fragment.

## Classical sources checked or used

- Conway, *On Numbers and Games*, and Gonshor, *An Introduction to the Theory of Surreal Numbers*: canonical background.
- Van den Dries and Ehrlich, *Fields of surreal numbers and exponentiation*, Fundamenta Mathematicae 167 (2001), 173–188, DOI 10.4064/fm167-2-3. The original paper was inspected, including the birthday bounds in Lemmas 4.1–4.2 and the proof of Proposition 4.7, and the epsilon-cutoff elementary-substructure statement in Corollary 5.5. Relevant original PDF pages were viewed.
- Ehrlich and Kaplan, arXiv:1512.04001v1: simplicity/initiality background.
- Hamkins's 8 April 2012 MathOverflow answer on definable ordinal-indexed dense maps into the surreal numbers: the density/V=HOD theorem is prior work and is not claimed here.
- Hamkins, Linetsky, and Reitz, arXiv:1105.4597v2: pointwise definable model background; existence theorems are not new claims of this manuscript.
- Jech, *Set Theory*, Third Millennium Edition (2003): OD/HOD, well-founded coding, and forcing background.
- Van den Dries, *Tame Topology and o-Minimal Structures* (1998): real closed field and o-minimal background.
- Shepherdson (1964): the classical integer-part/open-induction connection.
- Hamkins's March 2026 surreal-arithmetic announcement: credited as an announcement of related work, not treated as a proof source.
- The user-supplied Wikipedia article was read for motivation, not used as a theorem authority.

## Repository scope

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned snapshot: `9a385d3957bdfe3d9ea79f9a524751c90bd2c894`.

The connected GitHub interface was used to inspect the repository README, recursive file tree, report catalogue, and detailed report guides. Closely compared report directories were:

- `docs/foundations-and-computation/surreal-fields-across-universes/`
- `docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/`
- `docs/surreal/omnific-diophantine-geometry/`

The guide/cross-reference for the omnific Diophantine report and the catalogue were also used to identify the prior set-sized quotient report. A complete independent proof audit of these reports was not performed. This limited scope is stated in the manuscript. No repository files were modified.

Detected overlaps deliberately not claimed as new:

- Full-class denominator clearing and Frac(Oz)=No.
- Constant-term retractions, finite quotient classifications, and related omnific arithmetic.
- Closed/nowhere-dense old surreal fields in proper same-ordinal extensions.
- Birthday-enriched interpretations and bi-interpretations of set theory.
- Saturation and first-new-birthday results across universes, which are not re-proved here.

## Proposed contributions and novelty qualification

The proposed contributions are the bounded and local omnific code with two-way definability preservation; canonical bounded birthday escape; the bounded noncollection and model-definability tests; the explicit two-way normal-form uniformity gap; and the maximal initial elementary exponential core, strengthened by birthday-controlled denominators and normal-form heredity. The conditional finite-parameter discontinuity result is also proved.

Searches included “definable surreal,” “ordinal definable surreal,” “surreal HOD,” “definable omnific,” “first undefinable ordinal surreal,” and “definable surreal initial ordinal.” No matching statement of the complete coding/core package was located in the inspected sources. The search was not exhaustive; an equivalent theorem may exist under other terminology. Several underlying mechanisms are elementary once the published background is available. Novelty and correctness remain distinct questions.

## Finite checks

`verification.json` records the actual run. All checks passed:

- 8,191 finite bit-code/decoder cases, exhaustive for lengths 0 through 12.
- 4 malformed codes rejected.
- 555 exact rational compression/inverse pairs.
- 554 adjacent monotonicity comparisons.
- 1,161 finite floor-correction cases.
- 24 finite support-shift cases.

These are exact Fraction-based computations in finite formal normal forms, not numerical substitutions of a large real for omega. They do not verify satisfaction, HOD, arbitrary ordinal supports, the imported cutoff theorem, or the initial-core theorem.

## PDF checks

The PDF was compiled with LaTeX, references were resolved, and all pages were rendered for visual layout inspection. The build was checked for undefined references, multiply defined labels, and overfull boxes. No such warnings remained. Ordinary underfull-box warnings in bibliography paragraphs do not affect mathematical content.

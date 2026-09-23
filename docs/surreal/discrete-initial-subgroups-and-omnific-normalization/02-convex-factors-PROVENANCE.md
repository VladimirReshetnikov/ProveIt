# Provenance and proof-status record

Date: 23 September 2026.

## Repository and predecessor

Repository: https://github.com/VladimirReshetnikov/Surreal
Pinned inspection commit: `9693b28c24e6fcb317ce47969a40185c5dfef402`.

The review included the root README, the formalization ledger, repository directory/catalogue information, and the omnific-groups-and-lattices report guide. It did not constitute a claim-by-claim audit of the whole repository or a local Lean build.

The preceding project manuscript **Discrete Initial Groups and Omnific Normalization: Sign-tree surgery, a sharp image classification, and an Ehrlich–Kaplan question** (23 September 2026; `omnific_normalization.tex` and `.pdf`) was retrieved from the user's Library. Section 8 already contains a discrete splitting criterion, an initial realization of the quotient by the least-positive cyclic subgroup, and an integer-bottom suspension. It explicitly does not assert closure under arbitrary convex quotients. No repository path was established for this manuscript, and none is invented in the article.

The present article does not depend on that draft's separate proposed solution of the full discrete normalization question. Its needed suspension is reproved from the published initial Hahn criterion. The extension from the special discrete quotient to arbitrary convex factors is the central proposed contribution here.

## Principal published inputs

1. P. Ehrlich and E. Kaplan, *Number systems with simplicity hierarchies: a generalization of Conway's theory of surreal numbers II*, Journal of Symbolic Logic 83 (2018), 617–633. DOI: 10.1017/jsl.2017.9. The article uses the numbering of https://arxiv.org/abs/1512.04001v1 . Theorem 1 and its sufficiency proof provide the actual-normal-form initiality criterion; Lemma 3 describes initial real coefficient groups.

2. P. Ehrlich, *Number systems with simplicity hierarchies: a generalization of Conway's theory of surreal numbers*, Journal of Symbolic Logic 66 (2001), 1231–1258; corrigendum 70 (2005), 1022. Its divisible ordered-group initial-embedding theorem is also recalled in the preceding Ehrlich–Kaplan source.

3. E. Jeřábek, *Rigid models of Presburger arithmetic*, Mathematical Logic Quarterly 65 (2019), 108–115. DOI: 10.1002/malq.201800019; https://arxiv.org/abs/1803.05797v2 . Used for the classical characterization of Presburger groups and their coherent residue map, divisible kernel, and residue-injectivity rigidity mechanism. The elementary algebraic facts needed by this article are also proved directly.

4. N. Strickland, *Algebraic theory of abelian groups*, https://arxiv.org/abs/2001.10469 (2020), especially Example 8.27. The identification of Ext(Q,Z) with the profinite integers modulo the ordinary integers is classical. The article gives its own explicit factorial presentations and verifies the equivalence relation for that family.

5. V. Bagayoko and J. van der Hoeven, *Surreal substructures*, https://arxiv.org/abs/2305.02001 (2023), and the author-hosted text https://www.texmacs.org/joris/sss/sss.html . Related viewpoint only; no theorem from this source is an unproved dependency of the compression argument.

6. A. Enayat, J. D. Hamkins, and B. Wcisło, *Topological models of arithmetic*, https://arxiv.org/abs/1808.01270v3 (2020). Used only for background on internal arithmetic and factorials in fragments of arithmetic. The obstruction for nonstandard Peano models in the present article is proved using an explicitly defined factorial residue type.

Conway's and Gonshor's books are cited for standard surreal normal forms. Full bibliographic details appear in the PDF and LaTeX source. External papers and the predecessor manuscript are not redistributed in this package.

## Contribution and dependency map

| Result | Status and dependency |
|---|---|
| Retained-ancestor compression and nested coherence | Complete proposed proofs in Section 4; finite regression tests supplied. |
| Splitting of convex subgroup sequences by normal-form projections | Complete proof in Section 3; relies on the published truncation-closure property of actual initial groups. |
| Initial realization of every convex factor | Main proposed structural contribution; uses the projection lemmas, compression theorem, and published initial Hahn criterion. |
| Presburger initiality iff ordinary coherent residue image | Proposed surreal application; classical residue algebra and divisible-group embedding theorem explicitly separated. |
| Factorial family and nonsplitting test | Explicit construction and direct proofs; extension-class background is classical, not a new Ext computation. |
| Continuum many rigid noninitial groups, dense examples, omitted types, ultrapowers, and Peano obstruction | Complete deductions from the structural theorem and/or residue criterion; no independently certified priority claim. |
| Unit-preserving omnific embeddings | Direct consequence of the residue criterion and the ordinary-integer constant-term projection. |
| Surcomplex assertions | Rectangular additive/module extension only; not a multiplicative, differential, or exponential equivalence. |

## Verification and limitations

The final LaTeX build completed with no warnings, overfull boxes, or unresolved references. The PDF was rendered and visually inspected. These checks concern presentation, not mathematical certification.

The Python regression run passed. Its full counts are in `data/verification.json`. It does not verify arbitrary ordinals, class comprehension, the imported initiality theorem, completeness of Presburger arithmetic, recursive saturation, or nonstandard arithmetic. No proof-assistant checking is claimed.

Targeted source review did not establish a prior formulation of the main convex-factor theorem, but search coverage was not exhaustive. The draft therefore does not certify novelty or announce an independently validated breakthrough. It also does not claim a complete classification of initially realizable groups or a resolution of the full Ehrlich–Kaplan optimality question.

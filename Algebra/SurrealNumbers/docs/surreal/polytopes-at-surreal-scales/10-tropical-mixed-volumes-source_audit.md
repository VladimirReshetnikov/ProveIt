# Source and proof audit

## Scalar sources inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt  
Pinned commit: `6996fee43cc97b6c16351def7507d59a95bf62f0`  
Inspection date: 30 September 2026.

### Natural valuation

Path: `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceValuation.lean`  
Blob: `222abd29b3a8f1352b473633383e31e6088d4315`  
Read range: source lines 1–150.

Read definitions/theorems include `valuation`, its Archimedean equivalence, `valuation_mul`, `min_valuation_le_add`, `valuation_antitone_nonneg`, the finite/infinitesimal valuation criteria, `tMonomial`, and `valuation_tMonomial`.

### Real residue field

Path: `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceStandardPart.lean`  
Blob: `78e7c0a646da5f6b55774f5eebe6e411c4dca273`  
Read ranges: source lines 1–80 and 80 through the end.

Read definitions/theorems include `IsFinite`, `IsInfinitesimal`, `standardPart`, `standardPartHom`, `standardPartHom_surjective`, `mem_ker_standardPartHom`, and `standardPartQuotientEquiv`.

The total `standardPart` function is not used as a field homomorphism on infinite elements. The proofs always restrict ring-homomorphism operations to the finite valuation ring.

## What was not verified

No Lean build was run. No claim is made that mixed volumes over the actual surreal scalar implementation have already been formalized. No repository-wide audit was conducted, and no uninspected informal repository result is a proof dependency of the new arguments.

## Mathematical dependencies

The geometric input is classical finite-polytope mixed-volume theory and its fixed-finite-data transfer to real closed fields. The manuscript explains the transfer using triangulations and semialgebraic descriptions. Compression, block mixing, minimum-basis normalization, standard-part volume reduction, and the rank-profile encoding are proved in the article.

Brändén–Huh supply the classical Lorentzian and tropical M-convex background for general matroid basis polynomials. The strict Fano cubic has a separate direct Hessian-signature proof. The Fano representability contradiction and the quadratic Plücker amplitude obstruction are also proved directly. The rank-two tropical realization fact is classical; a finite construction over the specified ordered value group is supplied.

The fact that Lorentzian polynomials need not be convex-body volume polynomials, including the undeformed Fano support obstruction, is not claimed as new. The article does not claim to settle the distinct intersection-theoretic Fano question in June Huh's 2026 survey.

## Computation and document validation

`verify.py` was executed successfully with SymPy 1.14.0. Its results are saved in `verification.json` and `verification.txt`. All checks are exact. They validate finite identities and example data, not the universal mathematical theorems by enumeration.

The PDF was compiled successfully with pdfLaTeX via latexmk. The final LaTeX log had no overfull/underfull boxes, unresolved references, or warnings. The PDF was rendered with Poppler and visually inspected, including the title, contents, principal theorem, coefficient table, and complete-page contact sheets during preparation.

## Novelty boundary

This is a proposed research contribution with complete manuscript proofs, not an independent priority certification. The targeted literature comparison covered mixed volumes, Lorentzian polynomials, matroid support obstructions, and absolute/tropical Grassmannians, including relevant 2026 sources. A comprehensive search across all of valuation theory and polymatroid representability was not performed.

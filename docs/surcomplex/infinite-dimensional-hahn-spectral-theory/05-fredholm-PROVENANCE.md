# Provenance and proof-scope record

## Repository snapshot

Repository: `VladimirReshetnikov/Surreal`

Pinned revision: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`

Inspection date: September 22, 2026. Build and verification timestamps may
fall on September 23 in UTC; the article date is September 22.

The repository tree and documents were retrieved directly through the
GitHub connector. The comparison was targeted rather than an independent
review of every file or every proof. In particular, the following were
retrieved and used to select or delimit the subject:

- `README.md`
- `docs/README.md`
- `docs/surcomplex/infinite-dimensional-hahn-spectral-theory/README.md`
- `docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`
- `docs/surcomplex/dynamics-and-normal-forms/README.md`
- `docs/surcomplex/analytic-geometry/README.md`

The introduction and relevant scope passages of the infinite-dimensional
spectral manuscript were checked. Its Part I concerns bounded-operator
coefficients on `H((t^Gamma))`; its Part II concerns row- and column-finite
coefficients on `C^(I)((t^Gamma))`. The report explicitly excludes a
trace-class theory. Its constant-normal spectral formula and positive-order
range-defect factorization are predecessors, not discoveries of this paper.

Canonical source directory:

`https://github.com/VladimirReshetnikov/Surreal/tree/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/surcomplex/infinite-dimensional-hahn-spectral-theory`

## Primary literature

The article credits and uses:

- Conway and Gonshor: surreal normal forms and field structure.
- Higman: well-quasi-ordering of finite words.
- Poonen, *Maximally Complete Fields* (1993), Corollary 4: Hahn-field algebraic closedness.
- Kato, *Perturbation Theory for Linear Operators*: compact spectral and isolated-cluster perturbation inputs.
- Simon, *Unitaries Permuting Two Orthogonal Projections* (2017): the classical direct-rotation formula.
- Bornemann, *On the Numerical Evaluation of Fredholm Determinants* (2010), Section 3: ordinary trace-class determinant identities and classical references.
- Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques* (1962): prior non-Archimedean Fredholm theory, in a different operator category.

The accessed Bornemann, Simon, and Poonen PDF material was also inspected
through page images for the relevant formulas or context. Full citations
and links are in the self-contained LaTeX bibliography.

## Search scope

Targeted searches included the following terms and combinations:

```
"Fredholm determinant" "Hahn" operators
"Hahn" "compact operators" spectrum perturbation
"trace class" "Hahn series"
"Hahn" "Lidskii"
"Hahn series" "Fredholm determinant"
"Hahn" "trace-class" "spectrum"
```

No directly matching account of the exact theorem package or the explicit
trace/product counterexample surfaced in this targeted search. This is not
a proof that equivalent results have never appeared. Broad searches also
returned irrelevant material; those results were not used as mathematical
evidence. The claimed classical inputs are attributed to primary sources.

## Candidate additions

1. Exact arbitrary-rank spectrum and algebraic Fredholm spectrum for the
   stated noncommuting compact-residue operator class.
2. An explicit positive self-adjoint, coefficientwise trace-class example
   with no bounded-coefficient global Hahn unitary diagonalizer.
3. Divergence of the coefficientwise ordinary eigenvalue trace sum and
   determinant product in the same example, with exact boundary identities.
4. The support-controlled trace-class Fredholm alternative in the named
   nonnegative-valuation coefficient category, together with its finite
   coupling domain and analytic accumulation obstruction.
5. The distinction between invariance of the point spectrum and enlargement
   of the non-eigenvalue spectral monad under scalar-workspace extension.

The classical formulas, the inherited range-defect factorization, and the
Hahn support machinery are not claimed as new.

## Explicit non-claims

No named published open conjecture is claimed solved. No complete
classification of all bounded-coefficient Hahn operators is claimed.
No general positive spectral measure or global surreal Hilbert-space
spectral theorem is supplied. No equivalence with intrinsic nuclear or
compactoid operator ideals is asserted. No determinant is defined for
every negative-valuation trace-class Hahn series. No regularized spectral
product in every possible alternative category is ruled out. No Lean or
other proof-assistant verification is claimed.

The 1,268 finite checks test exact algebraic identities and recurrences;
they are not evidence of exhaustive priority, nor a replacement for the
infinite-dimensional arguments. The manuscript has not been independently
refereed.

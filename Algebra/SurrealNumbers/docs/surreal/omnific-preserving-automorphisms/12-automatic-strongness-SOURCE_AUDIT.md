# Source, proof, and novelty audit

Date: 23 September 2026.

## Exact claim boundary

The main claim is Theorem 5.5: **every unital ring automorphism of Oz extends
to an R-linear, strongly additive automorphism of No**. The consequence is
that the prior strong omnific-stabilizer factorization describes the entire
real omnific stabilizer. The manuscript retains the prior character
admissibility requirements; it does not claim that arbitrary coefficient
arrays define automorphisms.

The second central claim is the explicit family of **proper coefficient-
moving embeddings** of the full pair (No, Oz), with exact predicate reflection,
constant-term preservation, strong additivity, and real-image intersection.
The image has a nonzero constant-term annihilator. The construction uses a
chosen derivation of R and a rank-separated additive embedding of the surreal
exponent group; it is not an algorithm on arbitrary real or surreal inputs.

Additional proved statements include the scalar summability criterion,
constant-term covariance theorem, set-sized adjoint and retraction results,
a proper-class failure of representability, qualified surcomplex versions,
and the regular-uncountable support-bound variant.

All these claims have written proofs. Historical priority is not certified;
no named published conjecture is claimed solved, and no independent referee
or proof-assistant verification is represented as having occurred.

## Repository actually inspected

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned snapshot:

    a6c68ac3826ac337762b71a2ef901997d019260c

The connected GitHub reader supplied the repository root, documentation tree,
and recursive tree (the last identified the snapshot). The targeted content
comparison used:

1. `docs/README.md` — the report overview, retrieved near the pin.
2. `docs/surreal/omnific-preserving-automorphisms/README.md` — at the pin.
3. `docs/surreal/omnific-preserving-automorphisms/10-support-cut-source_audit.md`
   — at the pin.
4. `docs/surcomplex/three-duals-of-hahn-vector-spaces/README.md` — at the pin.

A directory read also confirmed the omnific-automorphism article and audit
files. Long guide responses were truncated; the scope claims used in this
manuscript were in the returned content. The full mathematical articles,
formalization ledger, and all supplementary files were not exhaustively read.
A local clone failed because network name resolution was unavailable. There
was no repository build or Lean run.

A reproducible raw-file prefix for pinned paths is:

    https://raw.githubusercontent.com/VladimirReshetnikov/Surreal/a6c68ac3826ac337762b71a2ef901997d019260c/

### Specific predecessor statement

The omnific-automorphism guide identifies its Theorem 5.1 as the **strong**
Oz-stabilizer factorization. It separately states that every field automorphism
preserving Oz, strong or not, fixes R and commutes with the signed projections
and floor. Its support-cut audit explicitly disclaims a classification of all
non-strong automorphisms. The new deduction is to combine those projection
facts with constant-term summability detection, eliminating a possible
non-strong real omnific stabilizer factor.

This is a logical comparison with the retrieved statement, not an assertion
that no unpublished or uninspected companion has independently proved it.

### Prior work explicitly credited

- Frac(Oz) = No is classical, not new.
- Divisible-ideal, multiplier-ring and coefficient-field reconstruction are
  prior repository material.
- The strong logarithmic-character framework and its summability requirements
  have published Hahn-automorphism antecedents.
- The convex-support criterion and strong omnific factorization are prior
  repository material.
- Finite-intersection support polarity and linearized finiteness-space
  duality are established antecedents, not invented in this manuscript.
- No prior fixed-field, monomial nondefinability, derived-length, or wreath-
  product result is presented as a new theorem here.

The repository's three-duals report concerns K-linear maps on vector-valued
Hahn spaces. The present adjoint statement concerns k-linear scalar maps on
full Hahn fields and the pairing ct(xy). The distinction is recorded without
claiming an exhaustive non-overlap proof.

## Primary public sources consulted

1. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
   of generalised formal power series*, arXiv:2107.03362v3 (2022).
   https://arxiv.org/html/2107.03362v3

   Used for the established strong Hahn-automorphism and character framework.
   The new manuscript does not assume that a bare character formula satisfies
   global support admissibility.

2. Elliot Kaplan, Lothar Sebastian Krapp and Michele Serra, *Decomposing the
   automorphism group of the surreal numbers*, arXiv:2509.22374v3 (2026).
   https://arxiv.org/html/2509.22374v3

   Used for the strong/non-strong distinction, normal-form background, and
   class-size conventions. The retrieved HTML gives different version and
   internal manuscript dates, so the source is identified by its version.
   No explicit automorphism example from that paper is needed for any proof
   here; all constructions used here are checked directly.

3. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
   generalised power series and omnific integers*, arXiv:1710.07304v5 (2024).
   https://arxiv.org/html/1710.07304v5

   Proposition 2.4.5 explicitly gives the cofinality-dependent fraction-field
   statement and records Frac(Oz) = No as Conway's Theorem 32. This prevents
   the erroneous transfer of that equality to every set-sized Hahn pair.

4. Richard Blute, Robin Cockett, Pierre-Alain Jacqmin and Philip Scott,
   *Finiteness spaces and generalized power series*, arXiv:1805.09836v1 (2018).
   https://arxiv.org/html/1805.09836v1

   Used to recognize and credit the finiteness-space precedent for support
   polarity and generalized power series. Ehrhard's original paper was not
   separately reviewed in full, and the manuscript does not pretend otherwise.

5. The user-supplied Wikipedia article:
   https://en.wikipedia.org/wiki/Surreal_number

   Orientation only, not a primary source for the new theorem or priority.

Sources were accessed on 23 September 2026. Keyword searches involving Hahn
fields, omnific integers, constant terms, strong automorphisms, embeddings,
and pairings were also attempted. Some returned largely irrelevant results.
They were not treated as reliable evidence that a theorem has no precedent.
The historical claim remains expressly limited.

## Critical mathematical checks

1. **Cancellation.** The summability detector chooses a triangular subsequence
   and coefficients in {0,1}; it works over finite as well as infinite fields.
2. **Summability before equality.** The target family is proved summable before
   its sum appears in the isomorphism argument.
3. **Surjectivity.** Every target scalar tester is pulled back. The embedding
   counterpoint supplies a specific missing test: t annihilates the image.
4. **Pi and units.** Pi is an ideal of its multiplier ring, not of the field.
   Units of k + Pi are exactly the nonzero elements of k, giving intrinsic coefficient recovery.
5. **Fractions.** The full surreal case uses an upper bound for a set support;
   no blanket fraction-field equality for set-sized exponent groups is used.
6. **Logarithmic shifts.** The least forbidden shift is not a finite sum of
   earlier allowed shifts, so its rational-power coefficient cannot cancel.
7. **Two-sidedness.** The signed-component criterion gives equality of component
   images using surjectivity and injectivity, not just forward inclusion.
8. **Taylor support.** The new exponent blocks are ordered lexicographically;
   pairs (g,n) are unique and negative blocks stay negative for every n.
9. **Inner versus outer exponent.** theta acts on the inner normal form of an
   outer exponent. Additivity, not multiplicativity, is the required property.
10. **Reflection.** J^{-1}(Oz) = Oz is proved using the unchanged constant
    coefficient and noncancellation of positive blocks.
11. **Set/class distinction.** Representing a scalar functional requires a set
    support; the ordinal-coefficient functional explicitly violates that
    representability while remaining well defined on each input.
12. **Surcomplex scope.** Natural valuation is assumed in the general theorem;
    conjugation compatibility supplies the real reduction in the special case.
13. **Restricted cardinals.** Regularity is explicitly used for support unions.
    No singular-cardinal theorem is claimed.
14. **Model-theoretic scope.** Automorphism invariance is not called first-order
    definability. The pair definition of R is separately justified by the
    existential Pi formula and the multiplier/unit formulas.

## Computation and build

`verify.py` completed with **17,774 exact assertions**:

- triangular detector: 10,800;
- monomial adjoints and transfer laws: 4,502;
- Taylor blocks and generalized binomial identities: 2,472.

These are finite sanity checks, not formal verification of the paper.
The program's seed is 20260923 and arithmetic uses `fractions.Fraction`.

The final standalone source was compiled with pdfLaTeX through latexmk.
It has no unresolved references, LaTeX warnings, overfull boxes, or underfull
boxes in the final log. The PDF has 24 pages and was rendered to page images
for visual review. `BUILD_AUDIT.json` records the exact final artifacts.
No font files, borrowed full papers, repository source trees, or failed clone
outputs are redistributed.

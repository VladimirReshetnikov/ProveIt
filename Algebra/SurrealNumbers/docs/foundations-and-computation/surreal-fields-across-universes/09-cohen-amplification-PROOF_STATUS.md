# Proof status and attribution

## Mathematical status

The manuscript contains full written proofs of the common-small-forcing lemma
and the Cohen-coordinate amplification theorem. The proposed new contribution
relative to the inspected ProveIt report is the same-spectrum/nonisomorphism
construction and its continuum-sized and surcomplex consequences. Independent
review is still needed; no result is claimed Lean-verified or refereed.

## Imported results

1. The fresh-sign gap correspondence was already proved in the repository's
   *Surreal Fields Across Set-Theoretic Universes*. It is re-proved in Section 2
   to fix conventions, not claimed as new.
2. The fresh-function cofinality reduction is established in Fischer–Koelbing–
   Wohofsky, Proposition 5.2. Section 3 supplies an explicit compatible code and
   records outer cofinalities.
3. Exact Easton-product spectra and cofinality preservation use their
   Proposition 4.10 and Theorem 4.24, under GCH.
4. Exact Prikry and Namba fresh-function spectra use their Theorems 7.21 and
   7.23, respectively. Namba's no-new-reals assertion requires CH. The Prikry
   construction requires a normal measure on a measurable cardinal.
5. Real-closed-field quantifier elimination, the surreal cut theorem, and
   standard-part facts are classical. The no-new-reals omega-saturation
   criterion and proper-class field back-and-forth are also already present
   in the repository and are credited.

## Sensitive proof points explicitly addressed

- The gap invariant counts all set-presented gaps, not arbitrary proper-class
  cuts. For general universe pairs, the spectrum itself can be a class.
- Ground regular cardinal labels and outer cofinalities are not interchangeable.
- Pointwise spectra are distinguished from a union of spectra over generics.
- The Easton closure definition retains the Mahlo exception.
- In the common forcing square the underlying poset is identical, not
  reinterpreted to acquire new conditions in the outer universe.
- Atomic forcing for ground names is proved absolute before canonical names
  are used to reconstruct an old-prefix function.
- Nice names lie in a specific ground set of graph names. No proper-class
  collection of all names is well-ordered.
- The size bound is strict and uses cofinality in the final universe.
- Agreement of spectra above omega and occurrence of the omega character
  are proved separately.
- Countable Cohen names for reals are coded by old reals; this proves both the
  no-new-reals comparison and the final-universe size of the index family.
- Nonisomorphism is a field claim: isomorphisms fix rational cuts. No claim
  of nonisomorphism of the pure order reducts follows from this argument.
- Surcomplex class isomorphisms use GBC with Global Choice. Simultaneous maps
  are one indexed class relation, not a set of arbitrary class objects.
- The involutions agree on C^M. For most members, agreement on C^N is proved
  impossible, not left as an unperformed choice.
- An arbitrary omitted set pair in a dense order need not define an
  endpoint-free gap. Section 2 gives the additional old-positive-bound
  argument needed for old surreal fields.

## Computational evidence

The recorded finite suite passed:

- 260,865 canonical option/cone tests;
- 260,865 comparison-antisymmetry tests;
- 5,704 block encoding/decoding tests;
- 183,103 block-prefix-dependence tests;
- three finite symbolic set-image examples.

These are not statistical or finite approximations to a forcing proof.
There are no finite fresh signs. The suite tests only the finite coding
formulas and arithmetic bookkeeping.

## Document checks

The PDF was compiled with pdflatex/latexmk, with references resolved and no
remaining missing-glyph, overfull-box, or undefined-reference warnings.
All pages were rendered with Poppler and inspected in contact sheets, with
representative technical pages inspected at readable resolution. These are
presentation checks, not mathematical verification.

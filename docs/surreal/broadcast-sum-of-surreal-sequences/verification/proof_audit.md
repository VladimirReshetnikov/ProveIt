# Proof and scope audit

This file records what supports the manuscript's claims. It is not an
independent mathematical certification.

## Provenance

- Lipparini's arXiv:2505.00424v2, Problem 7.5, is the selected open-ended target.
- The sign-truncation rule already appears in Remark 7.6(3).
- The source already observes termination; the manuscript supplies an explicit
  ordinal rank instead of claiming to originate that observation.
- The manuscript's strongest proposed contributions are universal
  number-valuedness, the finite-short-perturbation estimate, and the exact
  finite/infinite-upgrade classification.
- The literature search was limited. Absence of a discovered overlapping paper
  is not evidence of exclusive priority.

## Dependency order

1. Define prefix truncation maps, their legal witnesses, and finite exemptions.
2. Construct an ordinal rank from the plus and minus sign heights. Every move
   strictly decreases it.
3. Show truncations commute. A nonidentity truncation can be legalized by moving
   its threshold to the earliest remaining unprotected sign.
4. Show the earlier witness in a pair of opposite moves survives. This proves
   left-option/right-option separation by induction on rank.
5. Deduce numerical game values, relabelling, zero insertion, negation, and
   agreement with finite sums and the source's ordinal operation.
6. Prove a finite-short-perturbation estimate by induction on the natural sum of
   two ranks. When one matched action is idle, a finite sign-length budget drops.
7. Evaluate constant dyadic sequences and finite defects by nested induction.
8. Describe all Left and Right options of the explicit convergent family.
9. For finite E, use integer simplicity. For infinite E, identify mutually
   cofinal and coinitial option sets, then use the standard omega-map cut.
10. Compare with an independently evaluated larger geometric sequence.

## Subtleties explicitly addressed

- A map can cease to be legal at its original threshold after another move.
  Commutation alone does not settle this issue. The proof includes threshold
  adjustment and a surviving-witness lemma.
- No argument assumes coordinatewise monotonicity of the broadcast value.
  Monotonicity of ordinary finite surreal addition is a separate standard fact.
- A 'finite error' is a surreal bounded by an integer, not necessarily an integer,
  real number, or infinitesimal.
- Every index family is a set, so the recursive option collections are sets.
- A constant comparison in the finite-perturbation corollary uses the same
  index set as the input family. The constant-dyadic formula and its
  infinite-leading-scale consequence require an infinite index set. A finite
  family can be constant outside finitely many exceptions vacuously.
- A threshold can be a limit ordinal only if a witness sign exists at that
  position. It labels a sign, not a transfinite turn. The descending rank
  excludes infinite option sequences altogether.
- No options for either player means every coordinate is zero. Normal play
  ends as soon as the current player has no option, which can happen at a
  nonzero position. There is no common finite bound on play length; the
  article exhibits arbitrarily long alternating plays from `(omega, -omega)`.
- The ordinal rank uses ordinary ordinal arithmetic and finite natural sum.
  The dyadic multiples of omega use surreal field arithmetic.
- The exact constants theorem concerns 2^(-m), not all positive surreals.
- Finite-prefix evaluation is not a method for computing the infinite broadcast
  value; the manuscript explicitly disproves that limiting prescription.

## What was actually tested

The exact Python tests check finite strings, finite game cuts, commutation,
legal opposite-move diamonds, elementary invariances and dyadic sign formulas.
Their actual counts are in test_report.json. They all passed in the delivered
original run; the September 22 proof review did not rerun or change them.
Tests do not prove any assertion quantified over all ordinal-length strings
or all infinite input sequences.

## September 22, 2026 proof review

The repository review checked the definitions and written proofs in dependency
order, including the transfinite rank, commuting truncations, legalization,
number-valuedness, finite-short-perturbation estimate, and the nested constant
and dyadic classification arguments. It corrected two omitted index-set
conditions with the counterexample `B((1)) = 1`, whereas the countably infinite
constant-one value is omega. The constant-dyadic proof is now explicitly
carried out on an arbitrary fixed infinite index set; each step uses only
finite exceptions and finite subsets of arbitrary size.

The source's sign rule and ordinal restriction were rechecked against
arXiv:2505.00424v2, printed pages 34–37. This review is a mathematical reading,
not external referee approval or proof-assistant certification. Original code
and generated verification records remain unchanged.

The revised PDF was rebuilt with three `pdflatex` passes using the preserved
bibliography. It has 20 pages, 73 cross-reference labels, and 6 bibliography
entries. The final log has no warnings, undefined references, or overfull or
underfull boxes; a three-pass baseline rebuild of the original 19-page source
also had none. Physical PDF pages 5–7 and 10–12, containing the changed rule,
termination discussion, and constant-family arguments, were rendered and
visually inspected. `document_check.json` remains the original build record,
not a validation record for this revised PDF.

## Independent review still needed

A specialist should check the transfinite rank argument, the numerical comparison
induction in the finite-perturbation theorem, both nested inductions for constant
sequences, and the final coinitiality calculation. A formalization would provide
stronger assurance than these finite tests and repository proof review. No
external referee review or formalization is represented as having occurred.

# Proof and source audit

## Scope of the problem selected

Isa Vialard's thesis asks for compositional calculation and a deeper
interpretation of friendly order type (Conclusion, printed p. 109):
https://isavialard.github.io/home/mwqo.pdf

The report selects the finite specialization of that program. It does not
assert that the exact finite problem was separately published as a named
conjecture. The full infinite compositional program is not settled here.

## External dependencies

The friendly-order-type definition is Vialard's. The multiset-width theorem
w(M_DM(P)) = omega^f(P) is imported, not reproved or claimed as new:

- Published version: Definition 3.3 and Theorem 3.4, MFCS 2023,
  https://doi.org/10.4230/LIPIcs.MFCS.2023.87
- Thesis version: Definition 5.3.2 and Theorem 5.3.3, printed p. 74.

The binary ordinal-sum law is already published (MFCS Proposition 4.1(1));
a self-contained residual proof is supplied for the transfinite development.
The finite disjoint-union formula is not claimed as a new special case.
No unrestricted infinite disjoint-union or Cartesian-product formula from
an earlier source version is used.

The earlier preprint arXiv:2302.09881 uses "maximal safe order type". The
report fixes the later open-ended-bad-sequence definition throughout.

## Self-contained finite proof

1. Incomparability components are uniformly ordered.
2. An open-ended sequence omits at least one element of each component.
3. In a finite connected incomparability graph, one can delete a maximal
   poset element without disconnecting the graph, while protecting any
   specified minimal root.
4. Repeated maximal deletion chooses all but that root in each component.
5. Processing components in reverse order gives a global legal sequence.

This proves f(P)=|P|-c(Inc(P)) without importing any multiset-width result.
The width conclusion then additionally depends on Vialard's theorem.

## Additional statements proved in the article

- All maximum friendly subsets omit precisely one minimal element per
  incomparability component; their number is the product of those counts.
- Witness edges from the constructive sequence form a spanning forest.
- A lexicographic substitution formula with nonempty finite fibers.
- A Cartesian-product formula for factors of sizes at least two.
- Well-ordered sum law, and finite-component transfinite evaluation.
- Infinite graph-only obstruction: countably infinite matchings can arise
  as incomparability graphs of different friendly ordinal types.
- Sharp stripped bounds, extremal examples, and augmentation monotonicity.
- Generating function and fixed-rank polynomials for naturally labelled posets.

## Important edge conditions

- All graph component counts include isolated vertices.
- The empty poset has f=0 and its multiset order has width 1.
- A friend must be present in the current residual, not merely the original poset.
- Roots are minimal in their components, not necessarily globally minimal.
- Empty fibers must first be removed from the substitution base.
- Cartesian formulas treat empty and singleton factors separately.
- Transfinite summation uses ordinal addition in the displayed order.
- Set-sized posets and ordinary ZFC are assumed.

## Novelty and verification limitations

Audit date: 19 September 2026. The published article, the 2024 thesis, the
older arXiv text, the author's publication list, and targeted terminology
searches did not reveal the main finite component formula. This is not a
proof of novelty or a guarantee that no later solution exists.

The code's independent dynamic program uses only the residual recursion.
Its agreement with the graph formula is a finite test, not a proof for all
finite orders or for infinite ranks. Certificates are algorithmically
verified, but the English proofs have not been formalized or externally
refereed. No claim of Lean verification or expert peer review is made.

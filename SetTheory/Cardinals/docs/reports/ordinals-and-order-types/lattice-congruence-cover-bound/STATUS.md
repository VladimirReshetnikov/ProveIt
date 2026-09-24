# Status and claim boundary

Date: 20 September 2026.

## Proposed solution, with complete written proofs

1. For all finite nonempty lattices, an element with at least k upper covers,
   k >= 3, forces density at most 2^(-k). The dual lower-cover assertion holds.
2. Equality holds precisely for a k-atom length-two lattice with arbitrary
   exterior chains, including one-element chains at the glued endpoints.
3. In the nonextremal class the density is at most (3/4)*2^(-k); this is the
   exact second largest constrained density at every size n >= k+3.
4. The finer bound is I(P)*2^(-m-k), where P is the poset of distinct fan labels,
   I(P) its number of order ideals, and m the number of join-reducible elements.
5. If density is at least p, the source's skeleton has at most
   2*t*(max(2,t)+1) elements for t=floor(log2(1/p)).

All these statements are mathematical deductions in the article. None is
just an extrapolation from a finite computation.

## Completed computational checks

- All isomorphism classes through 8 elements are represented.
- Natural labellings retained: 4,008 (not isomorphism-class counts).
- Congruences counted over those labellings: 25,280.
- Upper-cover fans tested, including selected subsets: 6,292.
- Fans attaining the main bound: 20.
- Fans with exactly 2 labels: 1,137; with at least 3 labels: 108.
- Independent all-partition comparison through 7 elements: 371 lattices.
- Eight fully serialized examples.
- Thirty-five selected structured larger cases; largest size 32.
- All completed checks passed.

An exploratory run at n=9 exceeded the tool timeout before producing a final
record. It is excluded from every completed total and claim. The default
verification range is the completed range, n <= 8.

## What is not claimed

- Independent refereeing or specialist confirmation.
- Proof-assistant verification, Lean compilation, or a formal kernel certificate.
- Exhaustive novelty or priority certification.
- Novelty of the classical label/ideal representation, universal counting bound,
  principal-congruence identities, or small standard examples.
- Novelty of each k=3 consequence, which overlaps existing density classifications.
- Classification of all second-level extremizers.
- Optimality of the quadratic skeleton bound.
- A bound on the total number of elements from a density threshold alone.
- An exhaustive enumeration above eight elements.
- A solution of all finite-lattice congruence-density questions.

## Source status

The source suggestion is informal and unnumbered, immediately after Lemma 4.4
in arXiv:2603.11454v1, page 8. It is not called a numbered conjecture in the source.
The arXiv history and author publication list were checked. The latter reports
acceptance of the source paper by CUBO on 14 August 2026, and still dates the
linked target manuscript 12 March 2026. This publication status concerns the
source paper, not the present draft.

The all-k target was not found resolved in the consulted material. A search
failure is not proof that no prior solution exists. See notes/source_audit.md.

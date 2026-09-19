# Proof dependency map and audit

## Precise claimed theorem

For a finite poset P with n >= 2 and finite k >= 1:

    o(W_k(P)) = H_(N_k(P)),  H_m = omega^(omega^(m-1)).

I_k(P) is the finite poset of nonempty indecomposable word classes of lengths
1, omega, ..., omega^(k-1); N_k(P)=|I_k(P)|. All orders are quotiented by mutual
embeddability. Empty and singleton alphabets are handled separately.

## External mathematical inputs

1. Higman's theorem for finite words over a finite poset.
2. The de Jongh--Parikh maximal-linearization theorem and its standard calculus:
   induced-suborder monotonicity, monotone-surjection monotonicity, the product
   formula with natural multiplication, and the residual formula.

The finite-alphabet maximal-order-type formula is rederived in Appendix A.
The known tree/indecomposable correspondence is credited, but its bounded-height
version is also proved in the manuscript rather than used as a black box.

## Internal proof chain

Finite concatenation lemma -> periodic comparison -> finite canonical atoms
-> finite generator upper bound H_N.

Equal-length block lemma -> marker embedding u -> u b a^lambda
-> first-atom lower bound H_(N+1) on lambda-ended words.

New atom z not below any old generator -> z not embeddable in any old word
-> strictly increasing matching of displayed separators
-> lambda-ended coordinates cannot spill into a bounded initial separator
-> induced product layers -> one further exponent step.

A finite linear extension of the same-height atom poset, beginning with a
minimal constant atom, iterates the last step through all atoms of that height.
Induction on height matches the upper bound at every finite level.

## Fragile steps checked explicitly

- No global order reflection is claimed for semantic concatenation.
- Bi-embeddability preserves the exact ordinal domain length.
- A nonempty tail of a lambda-ended word has length AT LEAST lambda; it need
  not have length exactly lambda if several blocks remain.
- A tail of a single lambda-block has length exactly lambda.
- An image of length lambda inside a lambda-block is cofinal, not just infinite.
- The last-factor argument extracts a tail; it does not assert that the original
  embedding put an entire indecomposable inside one factor.
- The marker b need not land at the distinguished target marker. Landing earlier
  inside the target prefix still gives the required reflection.
- The direction needed when adding an atom is new NOT <= old, supplied by an
  increasing linear extension. Old <= new is allowed.
- The separator coordinate argument uses both boundaries: the preceding cofinal
  separator excludes spill to the left, and the following separator's first
  image provides a bounded interval excluding spill to the right.
- Different product layers cannot become equivalent: layer index is monotone
  in each embedding direction.
- Products are combined by an ordinary countable ordinal sum of linearized
  layers. There is no appeal to an undefined countable natural product.
- Canonical nodes include antichains of mixed lower heights. Restricting children
  to the immediately previous height would give incorrect counts.
- N_(k+1)=n+J(I_k)-1 counts all nonleaf nodes once, including nodes already present
  at earlier heights. It is not a recurrence depending on N_k alone.
- The all-height union is not evaluated by exchanging maximal order type and
  increasing union; that operation is not generally valid.

## Computational checks and limits

See data/verification.json. Exact atom counting uses two distinct recursions,
plus exhaustive subset checks where small enough. The symbolic omega-word
embedding algorithm is independent of the atom-counter implementation and
uses whole ultimately periodic omega-blocks, not finite unrollings.

The recorded tests all passed. No remaining mathematical gap was identified
in the internal review. This is not independent verification: the manuscript
and code were developed together in the same research session. No Lean, Coq,
Isabelle, or other kernel has checked the transfinite proof, and no external
referee has reviewed it.

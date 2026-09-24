# Source and proof audit

Date: 23 September 2026.

## Scope and baseline

User-supplied repository:
https://github.com/VladimirReshetnikov/Surreal

Recursive tree reference returned by the GitHub connector:
`343dc2c471212bb9b53ff4623bace2e1943f255b`.

Read/search access used the GitHub connector. A local clone was attempted but
failed because the container could not resolve github.com. No local repository
build, full source audit, or repository write was performed. This limitation
does not affect the standalone article or its delivered example verifier.

Repository inspection covered the root README, the report catalogue, and
selected guide content for these report directories:

- `docs/surcomplex/surcomplex-field-automorphisms/`
- `docs/surreal/omnific-preserving-automorphisms/`
- `docs/surreal/set-sized-quotients-of-omnific-integers/`
- `docs/foundations-and-computation/large-cardinal-embeddings-and-normal-forms/`

The omnific Diophantine report's coefficient/fraction-field reconstruction
material was identified through the root and omnific-preserving guides.
It is not represented as independently audited source text. The needed facts
are proved directly in Section 7 of the delivered article.

Some long connector responses were displayed with truncation. Claims of
repository coverage are confined to content actually inspected. A failed
keyword search does not establish that a theorem is absent from the repository.
The maintained guides already contain nonstandard plain real forms, phase
twists, and coefficient reconstruction; those are not claimed as new here.

## Primary literature checked

1. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
   of generalised formal power series*, Journal of Algebra 605 (2022), 339–376.
   DOI: 10.1016/j.jalgebra.2022.04.023.
   https://arxiv.org/abs/2107.03362
   The v3 PDF was read for the strong-automorphism convention and structural
   background. In particular, Definition 4.0.5 requires the inverse to be
   summable as well. The article uses the explicit all-families convention.

2. Bjorn Poonen, *Maximally complete fields*, L'Enseignement Mathématique
   39 (1993), 87–106.
   https://math.mit.edu/~poonen/papers/amsval.pdf
   Inputs: the support-product facts, maximality of full Hahn fields, and
   algebraic closedness for divisible exponents and algebraically closed
   coefficients. Theorem 1 and Corollary 4 were identified. The delivered
   article supplies a separate elementary nest-of-balls proof for its
   maximality use, rather than assuming a proper-class extension.

3. Keith Conrad, *The Artin–Schreier Theorem*.
   https://kconrad.math.uconn.edu/blurbs/galoistheory/artinschreier.pdf
   Theorem 3.1 and Section 4 supply the finite algebraically-closed fixed-field
   result and the order-two restriction. This input is applied only to the
   ordinary set field C. No class Galois theorem is assumed.

4. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra,
   *Decomposing the automorphism group of the surreal numbers*.
   https://arxiv.org/abs/2509.22374
   Version 3, 23 April 2026, checked as current literature context.
   No theorem in this delivery is presented as solving its unrestricted
   exponential-automorphism questions.

Conway's and Gonshor's standard books are cited for normal forms and surreal
cut interpolation; Lang is cited for classical field classification. No
verbatim excerpts from those books are included. The user-supplied Wikipedia
page was opened for orientation and is not used as a primary proof reference.

## Proposed contribution and priority boundary

The proposed contribution is the combination of:

- the explicit finite product section `m_gamma = product_g g(t^(gamma/n))`;
- its diagonal summability proof;
- the surjectivity reduction to maximal set-sized Hahn fields;
- preservation of negative support and the separate inverse-strongness proof;
- classification of strong valued Gaussian-preserving involutions and their
  fixed support rings;
- the Archimedean integer-part criterion and the exact 2^continuum count,
  with pairwise nonisomorphic fixed fields in the lower-bound family.

These conclusions are not asserted to be the first possible formulation in
valuation theory. The norm argument has familiar algebraic antecedents. The
search did not establish publication priority, and the evolving repository
was not exhaustively inspected. No unsupported assertion of novelty or
independent certification should be inferred from the term "theorem."

## Hypotheses that must remain visible

- The coefficient field is a set and has characteristic zero in the stated
  main theorem.
- The exponent group is divisible, and the Hahn field is full. For No
  exponents, every support and every summed family is a set.
- The finite action is valued and strong, and stabilizes both the coefficient
  field and the strictly negative-support part.
- In the Gaussian application, preserving Oz[i] supplies the last two
  stabilizations but does not silently supply valuedness or strongness.
- Both directions of a strong automorphism must preserve summation.
- A discrete ring need not be an integer part. The fixed-ring floor exists
  exactly for Archimedean coefficient real forms.
- The outer Hahn valuation is identified with the natural ordered-field
  valuation only when the coefficient field is Archimedean.
- The exact upper bound counts the specified strong valued Gaussian-preserving
  conjugacy types, not all involutions of the plain class field.

## Proof review checkpoints

1. A well-ordered monomial family remains summable under each action map.
   Its finite Cartesian-product family is summable; the norm family is a
   subfamily on the diagonal. This is the support justification.
2. Each norm monomial has the claimed value, so the least input exponent
   cannot cancel. This makes the extended map an embedding.
3. In the set case, the image is maximal and the ambient extension immediate.
   In the class case, close a set of exponents under the supports of the
   finite group images, using countably many set-sized stages.
4. Equality H(I)=I follows after surjectivity from the negative/constant/
   positive direct sum. It is not inferred from inclusion alone.
5. Constant-term preservation then yields inverse strongness through the
   coefficient-pairing test. The test needs all series as probes, not just
   individual monomials; the row-finite Baire lemma detects bad union support.
6. Gaussian coefficient recovery uses Frac(A)=K, I=intersection_n nA,
   (I:I)=k+I, and units(k+I)=k^*. The fraction assertion uses the fact
   that every set of surreal exponents has an upper bound.
7. Artin–Schreier is applied in C. Coefficientwise fixed forms are then
   transported through H, avoiding class-sized Galois assumptions.
8. The large family starts with real closures of Q(T0 union U) inside R.
   Rational cuts prohibit an isomorphism between different such subfields.
   Natural residue fields distinguish their full Hahn fields.

## Verification status

The article contains complete written proofs of the claimed implications.
They have been reviewed during preparation, but have not been checked by an
independent referee or a proof assistant.

The program `code/verify_finite.py` was run with N=12 and passed 3,751 exact
assertions. It checks only finite algebraic identities in Q(i)[u]/(u^12)
and a finite window of the lexicographic support example. These tests do not
verify the transfinite, class-theoretic, Baire, maximality, or cardinality
arguments. The PDF was compiled, rendered, and visually inspected; see the
separate build record for the final document checks.

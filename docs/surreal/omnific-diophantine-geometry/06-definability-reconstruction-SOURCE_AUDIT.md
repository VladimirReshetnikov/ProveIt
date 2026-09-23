# Source and novelty audit

Date: 23 September 2026.

## Scope

The user's request allowed either resolving known open questions or proving
interesting new theorems. This article takes the latter route, with qualified
novelty claims. It does not announce a solution of a named longstanding
factorization conjecture.

The repository snapshot examined was
`71e9606d297c9b98c732070dc462682cc6948981`.
The main README, `docs/README.md`, and the opening status/dependency discussion
of `docs/FORMALIZATION.md` supplied the collection map and verification status.
The opening 235 source lines of
`docs/surcomplex/surcomplex-field-automorphisms/article.tex` supplied the
relevant coefficient/character/real-form comparison. This was not a complete
read of every report in the repository. A failed or empty code-search result
was not treated as evidence that a theorem is absent.

The manuscript's own proofs do not depend on the correctness of unreviewed
repository theorems. Its phase-twist argument is supplied in full.

## Important prior work actually found

### Ordinary integers were already first-order definable

The MathOverflow user `nombre`, on 6 July 2018, explicitly noted that the
ordinary integers are definable in Oz by excluding nonzero solutions of
`x^2=2*y^2` in bounded intervals, and used this to observe nonsaturation.

Source: https://mathoverflow.net/questions/304290

The article therefore does not claim first-order definability or
nonsaturation as new. The proposed strengthening is a single quintic,
positive-existential definition with seven witnesses. The quadratic ideal
predicate is explicitly linked to the same prior obstruction.

### Logical weakness and axiomatization were discussed earlier

Emil Jerabek's 2011 answer discusses the omnific ring's logical properties.
The elementary retraction also transfers integer-coefficient polynomial
solvability directly to the ordinary integers. Thus undecidability of that
solvability problem is not a newly discovered consequence of the quintic.

Source: https://mathoverflow.net/questions/72691

### The normal-form algebra is classical

Conway and Gonshor are the classical sources. The author manuscript of
L'Innocente–Mantova, *A factorisation theory for generalised power series and
omnific integers*, v5, 22 January 2024, gives the precise support and
constant-term description used here. Its journal record is Advances in
Mathematics 442 (2024), 109513.

Source: https://arxiv.org/html/1710.07304v5
DOI: 10.1016/j.aim.2024.109513

No conclusion about the September 2026 status of unrelated factorization
conjectures is inferred from this 2024 manuscript.

### The intersective polynomial is classical

`H(T) = (T^2-13)(T^2-17)(T^2-221)` appears in Example 4 of Thai Hoang Le and
Craig V. Spencer, *Intersective polynomials and Diophantine approximation,
II*, arXiv:1309.2259v1. Its local-root property is credited and proved anew
for self-containment. The proposed contribution is its use as an order-free
nonzero certificate after Pell rigidity has forced a Gaussian constant.

Source: https://arxiv.org/html/1309.2259v1

### Phase twists are already in the repository

The repository report *Automorphisms of the Surcomplex Numbers* explicitly
constructs coefficient-fixing character twists moving the real axis.
The current article credits this. The extra assertion proved here is that
the displayed twist preserves the Gaussian omnific ring, giving a
nondefinability statement even after that ring is named.

### MRDP is an imported theorem

The computably enumerable classification uses the classical MRDP theorem,
not a new proof of it. The article proves the omnific guard-and-retraction
step and states the integer-coefficient and standard-support restrictions.
The four-square ingredient is classical and has a complete elementary proof
in Appendix A.

## Proposed contributions, with limits

- Explicit single-quintic definition of Z in Oz: degree 5, seven witnesses.
- Explicit Gaussian system: three equations, five witnesses, degrees 3,3,7.
- Diophantine constant-term graphs; degree-ten/eight-witness real version.
- Exact multiplier identity, used to define the actual coefficient field
  in the interpreted fraction field from the pure omnific ring.
- Real coefficient rigidity for all automorphisms of Oz, and the contrasting
  Gaussian preservation/nondefinability statements.

These exact formulas and the complete reconstruction package were not found
in the inspected material. The search is not exhaustive, so this is a
qualified novelty assessment, not proof of historical priority.

## Critical hypotheses checked in the proofs

1. Supports are reverse well ordered in the infinite-direction convention.
   The largest exponent exists; a smallest positive exponent is never assumed.
2. The equation defining the ideal uses a square root in the coefficient
   field that is absent from the fraction field of the constant ring.
3. Real sums of squares encode conjunction only in an ordered field.
4. Gaussian Pell coordinates need only be Gaussian constants, not real ones.
5. The intersective certificate is not a global definition of nonzeroness.
6. Coefficient reconstruction requires a nonzero exponent group.
7. The fraction field of a fixed Hahn subring need not be the full Hahn field.
8. Full surreal common denominators use bounds on set-sized supports only.
9. Universal multiplier predicates are used for automorphisms, not silently
   transferred through arbitrary nonsurjective embeddings.
10. The coefficient field is recovered as a set, not as a chosen monomial
    cross-section or a complete normal-form presentation.

## Verification boundary

The supplied Python program passed exact symbolic and finite congruence
checks. These are not proof-assistant verification. The written argument
remains subject to independent mathematical review. No Lean result,
repository build, peer review, optimality result, or priority certificate is
claimed.

# Source and novelty audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `37eefca1a309a967d8c8237606ccf6290475adfa`

The connected GitHub tools were used to read commit information, the documentation
catalogue, directory information, the rotation-quotient source audit, and substantial
parts of the trigonometry README and source-provenance inventory. Relevant paths:

- `docs/README.md`
- `docs/surreal/euclidean-three-space/10-rotation-quotients-SOURCE_AUDIT.md`
- `docs/surcomplex/trigonometry/README.md`

The repository's rotation report already proposes a universal set-sized quotient
for full surreal rotation groups. That is an acknowledged conceptual precedent.
The trigonometry report already covers additive period arithmetic, exponential
kernels, and profinite character defects. The present paper's ring/module theorem
uses multiplicative geometric divisibility, not those group-theoretic proofs.

A GitHub code search for `omnific` returned an explicitly incomplete result. It
was not interpreted as evidence of absence. This was a targeted comparison, not
a line-by-line audit of all reports, Lean files, or archived source packages.
No local Lean build was performed. The new proofs do not import a new unreviewed
mathematical theorem from the repository.

## Primary sources consulted

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
   power series and omnific integers*, arXiv:1710.07304v5 (22 January 2024),
   published in Advances in Mathematics (2024), article 109513.
   DOI: https://doi.org/10.1016/j.aim.2024.109513
   HTML: https://arxiv.org/html/1710.07304v5
   PDF: https://arxiv.org/pdf/1710.07304
   Relevant material: normal forms and support arithmetic; Theorem B, which proves
   the primality of omega^(sqrt(2)) + omega + 1; Proposition 8.2.1 on separated-scale
   division. Relevant PDF pages were inspected as images. The primality theorem is
   explicitly credited and not reproved or claimed as new.

2. Alessandro Berarducci and Vincenzo Mantova, *Surreal numbers, derivations and
   transseries*, arXiv:1503.00315 (2015).
   https://arxiv.org/abs/1503.00315
   Used for the established normalized surreal derivation with partial(omega)=1,
   which gives a class-valued counterboundary to set-valued derivation vanishing.

3. The Stacks Project, Section 10.39, *Flat modules and flat ring maps*, especially
   Lemma 10.39.3 on directed colimits of flat modules.
   https://stacks.math.columbia.edu/tag/00H9
   The paper uses the lemma only for a set-indexed directed union over a set ring.

Conway's *On Numbers and Games* and Gonshor's *An Introduction to the Theory of
Surreal Numbers* are cited as standard foundational references. Neither book is
represented as having been newly read in full for this task.

## Novelty assessment

Principal candidate contributions:

- The constant-coefficient map of the full omnific ring, and its D + I_k
  generalization, is universal for every set-sized unital ring target.
- Every set-sized module over the full ring factors through its coefficient ring.
- Explicit countable-support rings inside the surreals with a prescribed sharp
  lambda threshold for non-arithmetic ring images and module actions.
- Exact residue-field cardinalities, detection of each nonzero positive-support
  element at the threshold, and at least lambda non-arithmetic maximal ideals.

Secondary consequences, not independent priority claims:

- Classifications of set-sized quotients, profinite completions, and ideal closures.
- Infinite irreducibles' constant coefficients and invisibility to set ring maps.
- Set-valued derivation classification and the ordinary Gaussian 2-torsion exception.
- Exactly aleph_1 generators for the set-sized augmentation ideal; flatness,
  idempotence, flat dimension one of the quotient, and vanishing positive self-Tor.

The geometric identity is elementary Hahn algebra with a close separated-scale
precedent in the factorization literature. The use of cardinal collisions to
study set-sized observations also has a conceptual precedent in the repository.
No claim is made to an exhaustive priority search. Targeted searches did not
locate an identical principal theorem; this is a qualified novelty assessment,
not proof that no earlier publication contains it.

## Verification

The supplied Python program was executed successfully: 597 exact finite assertions
passed. It checks finite geometric/telescoping identities, truncated comaximal
identities, coefficient maps, finite-support evaluation, a Gaussian derivation
example, and gcd congruences. It does not verify transfinite Hahn summability,
class theory, infinite cardinal arithmetic, the maximal-ideal theorem, or novelty.

The LaTeX source was compiled, references resolved, and the PDF was rendered and
visually inspected. No proof assistant or independent referee verified the new
theorems. This manuscript is an AI-assisted research draft with full written
arguments and an explicitly limited finite computational check suite.

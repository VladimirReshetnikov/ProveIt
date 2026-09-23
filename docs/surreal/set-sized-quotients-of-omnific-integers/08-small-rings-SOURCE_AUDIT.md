# Source and novelty audit

Date: 22 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal\
Pinned commit: `37eefca1a309a967d8c8237606ccf6290475adfa`.

The repository was accessed through the connected GitHub tools. Material
actually inspected included returned root-README content, the research-report
catalogue `docs/README.md`, directory listings, and the complete
`docs/surreal/euclidean-three-space/10-rotation-quotients-SOURCE_AUDIT.md`.
A code search for “omnific” returned no results; this was not treated as proof
that the topic was absent from all files or archived manuscripts.

The rotation audit describes a universal set-sized group quotient result and
is acknowledged as a conceptual predecessor. Its complete mathematical article
was not re-audited, and no result here depends mathematically on it. This was a
targeted comparison, not an exhaustive audit of all repository reports.

A local clone attempt failed because network name resolution in the container
was unavailable. Connector reads succeeded. No Lean build or repository write
was performed.

## Primary mathematical sources

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
   power series and omnific integers*, Advances in Mathematics 442 (2024),
   article 109513. DOI: 10.1016/j.aim.2024.109513.
   Consulted arXiv version: https://arxiv.org/html/1710.07304v5
   Relevant comparisons: normal-form/Hahn background; Theorem B (the already
   proved primality of omega^(sqrt(2)) + omega + 1); Proposition 8.2.1
   (higher-scale divisibility). The elementary geometric mechanism used here
   is not claimed as an unprecedented observation.

2. Alessandro Berarducci, *Surreal numbers, exponentiation and derivations*
   (2020), arXiv:2008.06878.
   https://arxiv.org/abs/2008.06878
   Consulted for normal forms, Hahn summation, and distinctions between types
   of surreal differential structure.

3. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, LMS
   Lecture Note Series 110, Cambridge University Press, 1986. Included as a
   standard background reference; the complete book was not inspected during
   this session.

Targeted web searches for omnific ring homomorphisms, quotients, and
cardinal-sized integer-part residue fields did not locate an identical version
of the two main results. Numerous search returns were irrelevant. The search
is not sufficient to certify historical priority.

## Candidate-original contributions

- The universal quotient Oz -> Z for all set-sized ring targets, including
  noncommutative and nonunital variants.
- The corresponding Gaussian and other constant-ring statements.
- The all-cardinal construction: the ring-target threshold is kappa, while
  the positive-support ideal's generation threshold is cf(kappa).
- The derived small-module, ideal-closure, and all-small-target root-obstruction
  formulations, with conservative claims about priority.

## Established or elementary ingredients not claimed as principal novelty

Conway normal forms; Hahn real closedness; constant-coefficient retractions;
ordinary finite reductions; binomial root expansions; diagonal Hahn derivations;
and the known primality example from L'Innocente–Mantova.

## Verification boundary

The article contains full written proofs. All 1,277 finite test cases in the
accompanying Python script passed. No proof-assistant verification, independent
referee review, or certification of the entire cited repository was performed.
The PDF was compiled successfully and inspected for layout and cross-reference
problems. Those checks are not mathematical proof certificates.

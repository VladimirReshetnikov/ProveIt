# Source, novelty, and verification audit

Date: 22 September 2026.

## Repository snapshot and actual inspection

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `37eefca1a309a967d8c8237606ccf6290475adfa`.

Inspected through the connected GitHub reader:

- Recursive repository tree and the root `README.md`.
- Documentation directory listing and catalogue `docs/README.md`.
- The `docs/surreal/euclidean-three-space` directory listing.
- `docs/surreal/euclidean-three-space/10-rotation-quotients-SOURCE_AUDIT.md`.
- The `docs/new` staging directory listing.

The existing rotation-quotient audit explicitly treats universal set-sized
quotients of surreal rotation groups. The manuscript acknowledges that
precedent and does not claim that studying small quotients is itself new.
The arithmetic proof here uses geometric difference-divisor certificates,
not a rotation-group theorem.

This was not a line-by-line audit of the whole repository, its history,
every Lean declaration, or all research reports. Gamma–zeta ZIP archives
were visible in the staging directory but were not unpacked. No theorem
in this manuscript is inferred from unseen contents of those archives.

A local clone failed because network name resolution in the execution
container failed. The connector-based text inspection succeeded. No Lean
build was run. The repository was not modified.

## Primary mathematical sources

1. John H. Conway, *On Numbers and Games*, 2001 edition (first published 1976).
   Publisher metadata and relevant chapter descriptions were checked.
   https://www.routledge.com/On-Numbers-and-Games/Conway/p/book/9781568811277

2. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*,
   Cambridge University Press, 1986. DOI: 10.1017/CBO9780511629143.
   Publisher metadata and relevant chapter descriptions were checked.
   These books were not read cover to cover for this project.

3. Bjorn Poonen, *Maximally complete fields*, L'Enseignement Mathématique
   39 (1993), 87–106.
   https://math.mit.edu/~poonen/papers/amsval.pdf
   Sections 3 and 5, including the support/inversion background and
   Corollary 4 on algebraic closedness, were inspected. A relevant PDF
   page was also inspected as an image. The article uses these as
   established input, not as new results.

4. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
   generalised power series and omnific integers*, Advances in Mathematics
   442 (2024), 109513. DOI: 10.1016/j.aim.2024.109513.
   https://arxiv.org/abs/1710.07304
   The normal-form setting and factorization/primality scope were checked
   in the primary paper. Its proof of Gonshor's specified primality
   conjecture is not presented as new. Its deep factorization theorems
   are not prerequisites for this manuscript.

5. Vincent Bagayoko and Joris van der Hoeven, *Surreal substructures*,
   Fundamenta Mathematicae 266 (2024), 25–96.
   DOI: 10.4064/fm231020-23-2.
   https://arxiv.org/abs/2305.02001
   https://www.texmacs.org/joris/sss/sss.html
   This provides a published precedent for surreal self-similarity.
   No exhaustive comparison with every construction in that work is claimed.

6. Dan Abramov, *Conway-refinement*, public Lean development.
   https://github.com/gaearon/conway-refinement
   Its README was read using the GitHub connector. It reports a proof claim,
   formal declarations, and axiom checks while retaining mathematical
   interpretation/review caveats. The proof itself was not audited. No
   theorem in the new article relies on this development.

## Novelty assessment

Targeted searches combined "omnific integers" with "homomorphism",
"constant term", "set-sized quotient", "maximal ideal", "idempotent", and
"profinite completion". No identical statement of the principal package
was located. This does not certify priority or exhaust the literature.

Main candidate contributions:

- Universal constant-term factorization for all set-sized ring targets,
  including noncommutative and nonreduced targets.
- Support-controlled transfer of full-class fields after inversion of a
  purely infinite element.
- Exact polynomial kernels over compressed Hahn fields in the full
  binomial quotient, with no restriction on ambient exponents.
- The resulting compatible dyadic Cantor algebra and explicit orthogonal
  idempotents.

Small ideal/module/completion classifications and Gaussian variants are
identified as consequences and extensions. Classical normal forms,
Hahn-field closedness, geometric identities, and finite Chinese remainder
theorems are not claimed as discoveries.

## Verification boundary

- The article provides mathematical proofs of every asserted new theorem.
- 621 named exact finite checks passed in the included Python/SymPy script.
- Those checks do not verify proper-class arguments, arbitrary Hahn support,
  full surreal normal-form theorems, or historical novelty.
- The LaTeX source compiled without unresolved references, duplicate labels,
  or overfull-box warnings.
- The PDF was rendered and all pages were inspected in contact sheets;
  selected dense mathematical and reference pages were inspected individually.
- There was no independent referee review and no Lean verification.

Class rings and quotients are treated explicitly. No set of all proper-class
ideals, category whose elements are uncoded class functions, or class-sized
Zorn argument is used to infer a maximal-ideal existence theorem.

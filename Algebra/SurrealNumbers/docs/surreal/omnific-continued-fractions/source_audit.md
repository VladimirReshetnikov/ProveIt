# Source and priority audit

## Repository comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `958b5c4865819bd55ea1f5ffc050282aea7ef570`

Commit timestamp reported by GitHub: 2026-09-23T23:26:37Z.

The connected GitHub tool was used to inspect repository metadata and read:

- `README.md`
- `docs/README.md`
- `docs/surcomplex/differential-equations/README.md`
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`

The root and catalogue document an extensive body of surreal, surcomplex,
omnific, and foundational work. Their current omnific floor and normal-form
infrastructure motivates the proposed formalization route. A continued-
fraction report was not identified in the inspected catalogue.

This is not a claim to have searched every declaration, every report body,
every unintegrated manuscript, or the complete Git history. The repository
was not built. The new proofs do not depend on its advanced unrefereed results.

## Historical source requiring explicit credit

Yves Roggeman, *Continued fractions and surreal numbers* (1985), printed pages
31–70, received 15 June 1985.

Author-hosted record:
https://www.researchgate.net/publication/268854423_Continued_fractions_and_surreal_numbers

Author-hosted scan:
https://www.researchgate.net/profile/Yves-Roggeman/publication/268854423_Continued_fractions_and_surreal_numbers/links/57aaf38f08ae0932c970bfb7/Continued-fractions-and-surreal-numbers.pdf

All 21 scan pages were inspected as page images; the document has two printed
pages per scan after the first. Parsed text was not sufficient, so the images
were necessary. The journal/volume/issue metadata were not independently
established from the primary scan and are deliberately not invented in the
bibliography.

The scan already treats the omnific floor algorithm, associated classes of
points with one infinite code, their size and structure, periodic fractions,
and generalized continuation. Relevant portions include Section 3A on
associated-class inequalities, Section 3H on structure, Section 3I on
generalized fractions, and the later periodicity discussion. Consequently the
article explicitly disclaims novelty for basic nonuniqueness and large fibers.

The proposed contribution is the systematic valuation-ideal formulation and
its precise full-Hahn and algebraic-fiber consequences. A wider historical
concordance could establish that some of these are implicit in earlier work.
No exhaustive priority certification is claimed. The first research question
specifically requests that comparison.

## Standard foundations

John H. Conway, *On Numbers and Games*, Academic Press, 1976; second edition,
A K Peters, 2001.

Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, London
Mathematical Society Lecture Note Series 110, Cambridge University Press, 1986.

These are standard sources for the normal-form construction, surreal field
operations, cuts, and real closedness. They are imported as foundations, not
claimed to have been newly reproved or fully machine-verified in this task.

## Classical and formalized continued fractions

Gautam Gopal Krishnan, *Continued Fractions*, Cornell notes, 22 August 2016:
https://pi.math.cornell.edu/~gautam/ContinuedFractions.pdf

Manuel Eberl, *Continued Fractions*, Archive of Formal Proofs, 20 March 2024:
https://isa-afp.org/entries/Continued_Fractions.html

These support the classical real continued-fraction background. Eberl's
formalization is a real-number development; it does not certify the surreal
results in the present article.

## Research status

Written proofs and finite reproducible checks are supplied. No independent
referee report, comprehensive novelty search, Lean certification, or certified
resolution of a named longstanding open problem is claimed. The further
questions are a proposed research program, not all a catalogue of published
open conjectures.

No third-party paper scans or font files are redistributed in this package.

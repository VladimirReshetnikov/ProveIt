# Source and claim audit

## Repository snapshot

Repository: VladimirReshetnikov/Surreal

Commit: `fb5c4b530e3ec04b5661347d51d5382526d5aa02`

Commit metadata time: 2026-09-23T17:28:37Z.

The GitHub connector was used for source reads. The comparison was targeted: it was not a complete read of all 51 reports or all incoming manuscripts. The attempted checkout could not resolve the GitHub hostname in the container; no checkout or Lean build was completed. The connector reads remained available.

Inspected material included:

- Root `README.md` and `docs/README.md` for the project and report inventory.
- Directory metadata under `docs` and `docs/surreal/omnific-diophantine-geometry`.
- `docs/surreal/omnific-diophantine-geometry/README.md`.
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`.
- `docs/surcomplex/surcomplex-field-automorphisms/article.tex`, selected ranges 1–160, 300–550, 770–970, and 970–1080. Some long connector responses were truncated; the audit does not claim a full manuscript read.
- A repository keyword search for “omnific automorphism”, which returned no result and was not treated as proof of absence.

## Explicit antecedents

The repository's `saut:thm:shiftflow` constructs the positive fixed-shift derivation and its exponential. The present elementary formula is its specialization when the coefficient functional vanishes on the shift. The additional omnific constraint requires annihilation of the whole principal convex subgroup, not just the individual shift.

The repository also has monomial character twists and complex phase twists. The latter already preserve Gaussian omnific integers because supports are unchanged and constants are fixed. The present Gaussian construction is stronger in being a 1-automorphism, fixing every complete leading term, with arbitrary set-parameter fixing and genuinely multiterm images.

The omnific reports already study constant-term retractions, purely infinite ideals, quotients, and Diophantine applications. Those are not claimed as newly discovered here.

## Primary literature

1. J. H. Conway, *On Numbers and Games*.
2. H. Gonshor, *An Introduction to the Theory of Surreal Numbers*.
3. S. Kuhlmann and M. Serra, *The automorphism group of a valued field of generalised formal power series*, arXiv:2107.03362; Journal of Algebra 605 (2022), 339–376.
4. E. Kaplan, L. S. Krapp, and M. Serra, *Decomposing the automorphism group of the surreal numbers*, arXiv:2509.22374v3.
5. V. Bagayoko, L. S. Krapp, S. Kuhlmann, D. Panazzolo, and M. Serra, *Automorphisms and derivations on algebras endowed with formal infinite sums*, arXiv:2403.05827v2.

Primary online source versions were checked on 23 September 2026. KKS's v3 HTML shows an arXiv date of 23 April 2026 and an internal date of 24 August 2026; the article reports that discrepancy rather than inventing a publication chronology.

Search terms combined “omnific integers”, “automorphisms”, “integer part”, “Hahn”, “convex subgroup”, “logarithm”, “fixed field”, “definable”, and “monomials”. No exact formulation of the main convex-annihilator or relative elementary fixed-field theorem was located in the sources inspected. This is a limited novelty assessment, not a priority certificate.

## Claim hierarchy

**Candidate-original central statements:** Theorem 4.3 (exact convex-support criterion); Theorem 8.1 (relative elementary fixed-field hull); the exact strength of set-local multiterm symmetry inside the leading-term kernel and its group consequences.

**Consequences and supporting refinements:** exact displacement, rank dichotomy, common fixed field, intrinsic coefficient invariance, strong omnific stabilizer restriction, adapted derivation criterion, explicit nonnilpotent metabelian subgroups, and Gaussian analogues. Some may admit independent shorter derivations or precedents not found by the targeted search.

**Known framework, not a novelty claim:** normal forms, real closedness, negative-support integer parts, general monomial/kernel decomposition, positive fixed-shift exponentials, and the general automorphism–derivation correspondence.

**Not claimed:** a resolution of a named open conjecture; classification of all abstract omnific ring automorphisms; automatic strongness; global admissibility of every additive logarithmic character; definable-closure identification for arbitrary nonmonomial parameters; a generation theorem for the whole kernel; preservation of the global surreal exponential or omega-map.

## Proof audit highlights

- “Purely infinite” requires all outer exponents to be negative, not just the leading exponent.
- The necessity argument tests every logarithmic coefficient through a finite polynomial in rational powers. It does not infer support restrictions from a leading-term calculation.
- A strong automorphism is required to be strong in both directions. The explicit formulas construct strong inverses.
- One-shift summation is proved independently and used on whole summable families.
- General additive logarithmic monomial prescriptions are not asserted to be globally summable or surjective.
- Coefficient-functional extension uses a basis of a set-sized vector space, never a class-sized basis of No.
- Full-class fraction-field recovery is not asserted for arbitrary fixed Hahn workspaces.
- Relative elementary fixed fields are not silently identified with model-theoretic definable closure.
- Preserving an RV quotient pointwise is distinguished from preserving a chosen monomial representative map.
- Real and imaginary shear parameters preserve different expanded structures; an automorphism commuting with conjugation cannot move its fixed real field.

## Verification boundary

The supplementary script executed 7,062 passing assertions. These are finite rational and symbolic checks, not a proof-assistant verification, an implementation of arbitrary surreals, or an independent correctness review of the article.

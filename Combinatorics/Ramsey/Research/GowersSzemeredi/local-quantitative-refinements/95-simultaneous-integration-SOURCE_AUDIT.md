# Source and proof audit

## Checkpoint

The repository's `main` branch moved during preparation. The exact formal
interface read for the final crosswalk was:

- Commit: `c9a9f2662ac9929f6cfb836957452256ef7e601c`.
- Path: `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean`.
- Read range: source lines 1–170.
- Relevant details: `phaseTwist`, the factorial condition in `lemma_17_1`,
  and the corrected degree `k+1` and unnormalized Fourier-square threshold
  in `proposition_17_2`.

The content of this file is a set of formal interfaces. Its presence alone
is not treated as proof that every numbered assertion is verified; proofs may
also live in separate modules not audited here.

## Research comparison

Inspected the aggregate README in
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/`,
including source descriptions in the vicinity of entries 43, 46, and 47.
Targeted searches for alternating pencils and common isotropic refinements
did not surface a Ramsey manuscript on this exact simultaneous problem.
This was not an exhaustive comparison with all newly arriving ZIP archives.

Directly read the Library copy of `boolean_phase_integration.tex` (1938 lines),
including its primitive formula, obstruction quotient, and source lines
922–1074 containing the exact cubic energy/repair theorem. This earlier paper
is explicitly credited; the present paper does not rebrand the scalar theorem
as a discovery. No bytes of that earlier file are redistributed in this ZIP.

## Primary literature actually inspected

1. W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001), 465–588.
   Primary PDF, Section 17; rendered printed page 578 inspected. Its phase
   extraction is the motivating interface, not an assertion that finite
   Boolean vector spaces and cyclic groups can be identified.

2. J. Tidor, *Quantitative bounds for the U4-inverse theorem over low
   characteristic finite fields*, Discrete Analysis 2022:14.
   Primary arXiv PDF 2109.13108, Definition 3.1 and Propositions 3.4–3.5.
   Used for the repeated-p integration criterion in the odd-prime extension.

3. Y. A. Drozd and A. I. Plakosh, *On nilpotent Chernikov 2-groups with
   elementary tops*, arXiv:1610.05030.
   Primary PDF, Section 2, Lemma 2.1 and Theorem 2.2. The displayed regular,
   infinite, and singular alternating block matrices were inspected as page
   images, not inferred from garbled matrix extraction.

4. I. Dolgachev and A. Duncan, *Regular pairs of quadratic forms on
   odd-dimensional spaces in characteristic 2*, Algebra & Number Theory
   12 (2018), 99–130; arXiv:1510.06803v2.
   Primary HTML, Section 4.1, Theorem 4.1, and its classical-source crosswalk.

Classical references Leep–Schueller (1999) and Waterhouse (1977) are identified
as the underlying classification sources. The former's bibliography and
cross-reference were checked through Dolgachev–Duncan, not by a full-text audit.
Direct access to Waterhouse's PDF was blocked. The accessible characteristic-
two formulation was checked in Drozd–Plakosh instead. No claim of reading the
blocked full text is made.

## Mathematical dependency audit

- Imported classical theorem: congruence decomposition of alternating pencils.
- Derived with proof: common-isotropic dimension n minus generic half-rank.
- Independent polynomial proof: a principal Pfaffian's degree pays for all
  rational rank drops, with no generic base-field evaluation assumption.
- Explicit construction: sharp unequal-budget frontier via scalar planes.
- Explicit construction: all feasible exact rank profiles using scalar planes
  and singular index-one blocks.
- Blockwise proof: defect zero classification and codimension-at-most-defect
  restriction, including irreducible sharpness in dimension four.
- Reproved credited analytic input: projective orthogonality, Boolean shear,
  and exact scalar cubic energy. No inverse theorem is hidden in this step.
- Main combination: simultaneous Boolean phase theorem and product slack law.
- Odd-prime extension: algebraic only; no unproved energy-to-rank estimate used.

## Claims deliberately not made

Publication priority; full Lean verification; global Szemeredi improvement;
common-coset energy retention; classification of common function extremizers;
function-level stability; complete minimum-dimension profile classification;
exact instance-optimal deletion cost; generic-rank classification for three
or more independent alternating forms.

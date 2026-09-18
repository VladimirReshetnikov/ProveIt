# Implementation status

## Requested property

A total unknot recognizer running in `n^O(log n)` for an n-crossing input diagram.
**Not established by this implementation.** The executable recognizer is a
different, complete algorithm with exponential worst-case complexity in grid size.

## What is complete and executable

| Component | Entry point | Scope / guarantee |
|---|---|---|
| Classical rectangular diagrams | `Grid` | Exact combinatorial validation and component count |
| Non-increasing moves | `Move.apply`, `moves` | Checked exchanges and destabilizations, cyclic neighbors included |
| Total exact recognizer | `recognize` | Unlimited finite search; completeness uses Dynnikov's theorem |
| Exact obstruction | `determinant` | Integer arithmetic; a value other than one proves nontriviality |
| Certificates | `verify_certificate` | Positive paths, determinant obstructions, closed negative state sets |
| Ball boundary patterns | `assess_pattern` | Polynomial criterion on validated spherical rotation systems |
| Rational H^1 | `rational_cohomology_basis` | Spanning-forest gauge and exact nullspace; integer representatives of a Q-basis |
| Compressed normal coordinates | `from_cocycle` | Normal triangle/quad multiplicities, cocycle validation, face matching |
| Potential arithmetic | `HierarchyPotential` | Correct base-(G+1) decrease and conditional iteration bound |

## What is NOT implemented

The attachment's page 109 names operations that are not calls in the recognizer.
There is no hidden QP backend. In particular:

1. No layered handle structure of a knot exterior with the initial Morse
   function and all embedding information required by the notes.
2. No compressed manifold cut retaining boundary-pattern provenance and
   attachment/gluing data. Integer normal coordinates alone are not such a cut.
3. No Agol-Hass-Thurston orbit machinery for connected components and compressed
   hierarchy operations. Large normal weights are not expanded, but this alone
   does not supply the missing operations.
4. No hierarchical multisurface construction with the required uniform
   pattern-complexity bound, nor compression with justified suffix reuse.
5. No constructive `USE CHEEGER REGION`, `HAKEN'S LEMMA`, or `WEAKLY REDUCE`
   transformation with a proved decrease of the relevant Heegaard complexity.
6. No proof of logarithmic hierarchy depth, polynomially controlled restarts,
   or the bit-size/runtime bounds needed to charge every operation to the
   original crossing number.

These are specific missing geometric constructions and quantitative proofs in
this deliverable, not a claim that they cannot be developed.

## Source distinction

The supplied February 2021 slides announce the QP theorem and describe the four
speed-ups on pages 66-74; the final flowchart is page 109. This report preserves
that claim as an announcement, not as a runtime guarantee inherited by unrelated
code. The additional paper examined was Lackenby, *Incompressible surfaces,
hierarchies and unknot recognition*, arXiv:2607.23350v1, 25 July 2026. Section 9
explicitly separates iteration counting from unspecified step costs and does not
there bound its parameters G and L. Nothing here asserts that a comprehensive
QP specification cannot exist elsewhere.

## Why common substitutions would be unsound

An arbitrary finite normal-surface search is not automatically QP. Bounding the
number of outer-loop iterations does not bound the work per iteration. A
machine-integer array of enormous normal weight is not a compressed structure.
Testing b1=0 is not, for an arbitrary input manifold, a proof that it is a ball.
Determinant one is not a positive unknot certificate. Reaching a search cap is
not a negative certificate. Universal proof search would require a concrete
formal bridge to a proved-fast program; none is asserted here.

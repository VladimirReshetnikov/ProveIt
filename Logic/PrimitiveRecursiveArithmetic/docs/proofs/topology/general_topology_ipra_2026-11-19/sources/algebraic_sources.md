# Sources for the finite algebraic chapter

Accessed 2026-11-19. These sources identify the requested classical targets
and their standard definitions. The chapter supplies its own finite arithmetic
proofs and states exactly which additional representation data it requires.

## Requested MathWorld entries

| Entry | URL | Browser reference |
|---|---|---|
| Betti Number | https://mathworld.wolfram.com/BettiNumber.html | turn366437174view0 |
| Euler Characteristic | https://mathworld.wolfram.com/EulerCharacteristic.html | turn366437174view1 |
| Sheaf | https://mathworld.wolfram.com/Sheaf.html | turn366437174view2 |
| Sigma-Algebra | https://mathworld.wolfram.com/Sigma-Algebra.html | turn366437174view3 |
| Stalk | https://mathworld.wolfram.com/Stalk.html | turn921308795view0 |
| Genus | https://mathworld.wolfram.com/Genus.html | turn921308795view1 |
| Subsheaf | https://mathworld.wolfram.com/Subsheaf.html | turn921308795view2 |
| Sheaf Section | https://mathworld.wolfram.com/SheafSection.html | turn921308795view3 |
| Restriction of a Sheaf | https://mathworld.wolfram.com/RestrictionofaSheaf.html | turn921308795view4 |
| Restriction Map | https://mathworld.wolfram.com/RestrictionMap.html | turn921308795view5 |
| Sheaf of Rings | https://mathworld.wolfram.com/SheafofRings.html | turn921308795view6 |
| Coloring | https://mathworld.wolfram.com/Coloring.html | turn921308795view7 |
| Presheaf of Categories | https://mathworld.wolfram.com/PresheafofCategories.html | turn921308795view8 |

## Primary mathematical references

- Allen Hatcher, *Algebraic Topology* (author's PDF), Chapter 2, especially
  simplicial homology, chain homotopies, cellular homology, and surface
  computations: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf . Browser
  reference: `turn704897624view0`.
- Stacks Project, Tag 006S, *Sheaves*: the sheaf axiom, the empty-set section
  condition, and sheaves of functions:
  https://stacks.math.columbia.edu/tag/006S . Browser reference:
  `turn704897624view1`.
- Stacks Project, Tag 0078, *Stalks*: germ equivalence, stalks, and detection
  of equality of sections: https://stacks.math.columbia.edu/tag/0078 .
  Browser reference: `turn704897624view2`.

## Scope qualifications

- Homology invariance is proved for supplied finite chain-homotopy
  certificates. No unrestricted singular-homology comparison is assumed.
- The genus formulas concern the specified polygonal cellular presentations;
  they are not a proof of the surface classification theorem.
- The set-valued finite sheaf theorems do not prove descent for categories.
  Finite category-valued restriction diagrams and their coherence equations
  are specified as bounded data to be checked.
- The sigma-algebra entry is treated by finite generated Boolean algebras
  and by finite or stabilization-certified unions. A uniformly computable
  Boolean code for every unbounded PR-enumerated union is impossible even
  on a singleton, by the halting reduction given in the chapter.
- A09 is a degree-plus-one coloring theorem and A10 is the odd-cycle
  alternative; neither is a claim to prove the four-color theorem.

## Validation

`code/algebraic_checks.py` uses exact integer and rational arithmetic. It
checks all 167 simplicial complexes on four available vertex labels, 340
elementary collapses, 5,103 prism equations (including degenerate maps), all
1,100 loopless graphs with at most five vertices, 689 finite generator
families for Boolean algebras, and 2,744 compatible function-gluing families.
The results are recorded in `validation/algebraic_checks.json`.

`lean/AlgebraicBlueprint.lean` compiles with Lean 4.32.0 and contains no
proof holes. Its completed proofs are a homotopy-on-cycles lemma for integral
finite chains, Euler telescoping from supplied rank-nullity data, and
function-gluing compatibility/uniqueness. Its matrix-reduction and complete
finite-sheaf targets are definitions of propositions, not assumed axioms.
The axiom printouts are in `validation/algebraic_lean.log`; no completed
theorem uses `Classical.choice` or `sorryAx`.

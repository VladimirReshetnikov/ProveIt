# Sources and provenance

Access date for web sources: 2026-11-16.

## Article and classification

- Wikipedia, “Pentagonal tiling,” current English page:
  https://en.wikipedia.org/wiki/Pentagonal_tiling
- Michaël Rao, “Exhaustive search of convex pentagons which tile the plane,”
  arXiv:1708.00274 (2017): https://arxiv.org/abs/1708.00274
- Michaël Rao, author publication list.  On the access date the exhaustive
  pentagon work appears under “Manuscrits/Soumis,” not under “Publications”:
  https://perso.ens-lyon.fr/michael.rao/publi.php?lang=fr
- Casey Mann, Jennifer McLoud-Mann, David Von Derau, “Convex pentagons that
  admit i-block transitive tilings,” Geometriae Dedicata 194 (2018), 141-167,
  arXiv:1510.01186.
- Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*, 1987.

## Exact coordinate reconstructions

- Jolu Mij, Type 14 exact construction and diagram:
  https://jsfiddle.net/jolumij/fzu3jw23/
- Jolu Mij, Type 15 twelve-tile construction and lattice vectors:
  https://jsfiddle.net/jolumij/1qh7zav9/
- The Tiling Atlas, Type 15 parameter summary:
  https://www.thetilingatlas.com/pentagons?type=15

The JavaScript coordinates were not trusted numerically.  They were rewritten
as exact rational/quadratic expressions and independently checked by
`code/verify_pentagonal_tilings.py`.

## ProveIt baseline

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Main commit observed on 2026-11-16:
  `d91fc1854ebe1f4be70f5c690b6180aca57cc937`
- Reused checked source locations:
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
  - `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/`

The repository README states that research proof packets are filed as delivered
and are not independently verified.  This package therefore reuses only the
checked calculus/derivation library as a trusted dependency and treats packet
arguments as design references.

## Original work in this archive

The following are newly assembled and checked for this delivery:

- strengthened regular-pentagon obstruction allowing T-junctions;
- a generic finite periodic-certificate specification and constructive
  soundness proof plan;
- exact rational Type 1 cell;
- exact regular-hexagon Type 1 and Type 3 subdivisions;
- exact Type 15 twelve-tile certificate with derived finite overlap radius;
- exact Type 14 ordered-quartic algebra, full congruence, convexity, separation, and connected local patch;
- exact triangle, square and hexagon nonconvex subdivisions;
- exact dodecahedral coordinate/incidence certificate;
- the fifteen-entry linear angle ledger; and
- the object-iPRA module plan.

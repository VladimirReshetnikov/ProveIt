# Proof and verification audit

## Logical dependencies

1. Reversal-orbit reduction: reproved; matches Davies's accessible-automaton
   formulation and fixes the composition convention.
2. Rightmost singular factor: a word containing s is written u o s o p^j.
   The collapsed graph edge uses p^(-j), not p^j; the graph includes all
   integer translates, so this is legitimate.
3. Graph classification: same-cycle displacement yields d cycles of length
   L; L=2 means an ordinary edge. Cross-cycle pairs yield d complete
   bipartite components by the generalized CRT.
4. Universal upper bound: each of the two homogeneous letter cases has its
   own bound. Every mixed case has an entry in the complete finite list.
5. Infinite range: n>=26 uses exact integer anchor inequalities and monotonic
   ratios. No numerical extrapolation is used.
6. Finite range: n=4..25 has 2,082 complete structural entries. Both programs
   recompute every entry; they do not just compare the displayed minima.
7. Attainment at n>=7: imports the published U_(A,B) generation theorem;
   the coloring-saturation argument itself is proved in full.
8. Attainment at n=4,5,6: full BFS orbit closure, checked with tuple and
   base-four integer encodings. Original automata are accessible and minimal.
9. Rigidity: equality first forces the optimal cycles and no within-cycle
   collision. The unique-cross-equality colorings then exclude two double
   fibers. Saturation is an explicit additional condition, not presumed.
10. Stability: a nonfull cyclic orbit has size at most AB/2 because its size
    divides AB. The strict near-maximum inequality is intentional.
11. Missing orbits: exact least periods are counted separately when a side
    is constant. The 2+2 palette formula applies only when both are nonconstant.
12. Recurrence minimality: all four Fourier modes at both exponential scales
    are nonzero; the polynomial term forces root 1 of multiplicity three.
    Finite recurrence tests are supplemental, not the minimality proof.

## Specific boundary checks

- The formula for the closest coprime split is used only for n>=7 in the
  main statement. The three smaller values are stated separately.
- The n=6 witness has two triangular collision components, not one C_6.
- Proper coloring orbit bounds do not imply generic improper saturation.
- The 24AB penalty assumes injectivity on both cycles and proper initial
  output. It is not asserted without those hypotheses or as a sharp bound.
- The primitive binary words on each optimal cycle use both colors because
  A,B>1. Their palettes must be disjoint, so four outputs force exactly 2+2.
- The count 6*P_2(A)*P_2(B) concerns output maps on the fixed standard
  transition pair, not all transition-output triples or all isomorphism types.
- A reverse-state BFS is not an exhaustive enumeration of all n-state
  automata. Universality comes from the structural bounds.
- Two code implementations are independent only at the implementation
  level. They share the mathematical certificate principle.

## Actual execution record

Producer: PASS.
- 2,082 structural entries, n=4..25.
- BFS witnesses, n=4..9.
- Complete missing-state inventories checked against BFS, n=7,8.
- Algebraic inventories, n=7..100.
- Recurrence regression, n=22..500.

Independent checker: PASS.
- Re-enumerates and recomputes all 2,082 structural entries.
- Base-four integer BFS for n=4..8.
- Exact threshold anchor arithmetic.
- Imports no producer code.

The JSON records in data/ are the execution outputs. The finite certificate
and scripts are part of the proof package; no proof-assistant kernel check,
external expert referee report, or community acceptance is claimed.

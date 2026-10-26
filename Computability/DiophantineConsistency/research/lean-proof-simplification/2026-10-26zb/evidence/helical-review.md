# Native proof proposals at 29936089835c0c55cca81edc86b4fb0c70ce34d5

## 1. Straighten a helical orbit using period one

Source: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalQuotient.lean`, `row_zero_of_helix`, lines 22-39.

Pinned source: https://github.com/VladimirReshetnikov/ProveIt/blob/29936089835c0c55cca81edc86b4fb0c70ce34d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalQuotient.lean

The existing theorem derives T(x,t)=T(x+wt,0) from the helical period (w,-1) by separate positive and negative integer induction branches. Define F(k)=T(x+wk,t-k). The hypothesis says F(k+1)=F(k), so F has period 1. Mathlib's `Function.Periodic.int_mul` gives period t, and its `eq` theorem gives F(t)=F(0). Simplification yields exactly the old conclusion, including negative t and arbitrary signed w.

The replacement preserves every argument, theorem statement, and executable definition. No positivity or divisibility premise is introduced. It removes 11 physical source lines: the declaration drops from 19 to 8 lines; the whole module from 147 to 136. The prototype compiles with Lean 4.32.0 and reports exactly [propext, Quot.sound].

Novelty: the exclusion audit found no helical-orbit/period-one proposal. Earlier packet u proposes integer induction on an interval and shared-edge row construction; earlier cell-equivalence suggestions concern aligned cell reindexing. Neither removes this two-sided helix induction. The narrow new contribution is the application of a one-dimensional period-one orbit to this actual theorem, not the invention of general periodicity.

Artifacts:
- `HelicalOrbit.lean`: standalone checked theorem and axiom output.
- `proposed/DiophantineConsistency/WangTiles942HelicalQuotient.lean`: complete proposed module.
- `helical-orbit.patch`: exact patch.
- `helical-metrics.json`: source line accounting.
- `helical-build-records.json` and `logs/`: complete-module, client and endpoint audits (inspect current status).

## 2. Optional rank ordering through C+qF

Source: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRankVariation.lean`, `windowRank`, `rank_strict_decrease`, `core_rank_strict_decrease`.

Pinned source: https://github.com/VladimirReshetnikov/ProveIt/blob/29936089835c0c55cca81edc86b4fb0c70ce34d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRankVariation.lean

For fixed q, MC, MF and J, put P=C+qF and K=(MC+qMF)J. The actual definition becomes
rank(C,F)=(q^2-P)(q^2-1)+K.
If q>1 then q^2-1>0, so
rank(C',F')<rank(C,F) iff P(C,F)<P(C',F'),
and similarly for non-strict order and equality.

This is a useful optional API for future order clients: the exact correlated-update formula is one way to prove potential increase, whereas the comparison theorem accepts arbitrary changes of C and F. Existing exact rank variation formulas remain available whenever the exact amount of rank decrease is needed.

The file `RankPotential.lean` reproduces the existing windowRank definition literally in an isolated namespace and checks the affine shape, strict comparison, equality comparison, weak comparison, correlated increment formula, equal-potential fiber and q=1 degeneration. The comparison theorems use only the standard axioms propext, Classical.choice and Quot.sound. The prototype is additive: no immediate net source saving is measured or claimed.

Novelty: prior packet u's stronger native rank envelope bounds the magnitude of a source-derived rank. It does not factor exact comparison and equality through C+qF. The exclusion audit found no equivalent proposal.

Scope restrictions:
- The same q, MC, MF and J must appear on both sides; arbitrary changes to those ports alter the constant term.
- The comparison theorem needs q>1. At q=1 the rank is independent of C and F.
- Equality of rank gives equality of scalar potential, not equality of the pair (C,F). The family (C+qk,F-k) has unchanged potential.
- Positive integer scaling need not be surjective onto all integers; this is not an OrderIso from all integer potentials to all integer ranks.
- The API does not construct a digit mutation, establish carry validity, or solve controller completeness. It only reduces a resulting rank comparison to an elementary scalar inequality.

A concrete research question is whether an actual valid controller mutation can certify the potential increment directly, avoiding an otherwise unnecessary intermediate exact F-increment lemma.

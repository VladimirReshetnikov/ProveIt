# What polynomial recentering can and cannot improve

## New theorem, unchanged witness

This component contributes a restricted optimality theorem, **not a new
numerical endpoint**. In the exact free-scale eleven-integer frame retained
from Round 18, every nonzero constant radical weight and every integer
polynomial center independent of the coordinate `n` has total degree at least
300. The byte-identical Round 18 equation `free_whole_center11_c300.json`
attains 300 in 148 live binary arithmetic operations.

The complete proof, including all three center-degree cases and the decisive
negative-square highest homogeneous part of the guard, is in
`SCALAR_FIXED_FRAME_DEGREE_FLOOR.md`. The exact attaining-center remainder,
actual nonzero leading coefficient, ordinary even-weight/center equivalence,
and all eleven-variable formulas are retained in `BASELINE_PROOF.md`. That
file is the unchanged original proof; its references to four endpoints describe
the historical Round 18 result, not four newly released graphs. Only its
300/148 graph is retained here.

## Logical calibration and its scope

The fixed six numerals are the authentic Round 18 tuple, reconstructed from
complete literal payloads and the finite recipe in `coefficients/`. No port is
an extra quantified unknown. `BASELINE_PROOF.md` proves that, for every nonzero
even weight and every integral center, the projection of the integer zero set
onto the ten outer coordinates equals that of the retained Round 17 source.
In particular this applies to the displayed attaining 300/148 graph.

The proof explicitly excludes zero carrier scales, separates both complex and
real squareclasses, handles the auxiliary denominator by integer descent, and
restores an actual old zero. Its converse fixes the strong Pell pair before
requesting an interpolation residue. `source/` retains the signed Pell/rank,
intersective polynomial, supported-modulus interpolation, native/compiler and
finite syntactic-refutation dependencies. `SOURCE_PINS.json` authenticates
those retained source bytes. Therefore the inherited ordinary theorem yields,
provably in ZFC, that nonexistence of an integer zero of this fixed polynomial
is equivalent to syntactic Con(ZFC). Neither side is proved true here.

The degree-floor theorem does not use that logical calibration, existence of
any zero, or an assumption about consistency. It concerns the literal
polynomials at the fixed authentic coefficient tuple. It holds for every
nonzero integer weight, although even weights are the ones covered by the
retained zero-existence equivalence. It is **not** a global lower bound for
Diophantine consistency equations in eleven variables.

## Finite certification

`check.py` is independent of `build.py`. It reconstructs all six actual
numerals, verifies source pins, binds every live arithmetic gate against free
polynomial identities, and certifies the actual degree-300 leader through the
exact center-remainder cut. `audit_mutations.py` rejects both alternative
operation labels at each of the 148 arithmetic gates, 296 mutations in total.
`check_scalar_top_forms.py` independently propagates all complete highest
homogeneous forms needed by the new lower-bound theorem, with no producer or
checker import. Every check runs identically with normal Python and `python -O`.
`replay.py` repeats the checks in a clean temporary copy and verifies
byte-identical reconstruction of the graph.

These finite algebra checks do not substitute for the unbounded ordinary
number-theoretic and syntactic-calibration dependencies. No new end-to-end
proof-assistant certificate is claimed.

## Consequence for the next search

Further polynomial recentering in this exact constant-weight frame cannot
lower degree below 300. A lower-degree endpoint must change an excluded part
of the construction, such as the carrier, guard, radical architecture, or the
outer coordinate chart. No such change is asserted valid in this component.

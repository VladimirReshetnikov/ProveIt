# Independent audit of the Round20 finite signed chains

The selected `signed/package/verify.py`, `check_sources.py`, and retained
`inherited_free/check_factorial_free.py` were read, and the full package
was replayed in normal and optimized Python. Both pass all five endpoints
and all16 listed corruption controls. Receipts are `SIGNED_NORMAL.json`
and `SIGNED_OPTIMIZED.json` with their corresponding logs.

## Literal semantic boundaries

The Shared source is reconstructed from the full common252 factored source,
not trusted by its label alone. The exact replacements are the deterministic
comparison factor f=(1-A)H_p and ordinate residue h moduloC; all fourteen
both-coordinate orientation terms are preserved. The seven removed rows
are the three private front guards, two original ceiling rows, the old
unused output bound, and its old BF multiplication gate. The literal absence
of the removed ceiling/remainder/slack coordinates from all remaining rows
is checked. The added rows are affine oddness q=2z+1, Bv=M andMF=vV+S;
the shared budget gains the single additional squareS^2. These correspond
exactly to the independently accepted unbounded proof in
`PROOF_SPHERE_SIGNED_FACTORIAL.md`.

The factorial-free source checker independently identifies each old power
base gate by its full polynomial, changes the actual base in its frame,
retains the raw index with F^2, adds odd-square beta andradix definitions,
and changes the self-radix offset soH=2+sumactualrepresentatives. Its
source aliases the old power output toF, proving the old output coordinate
absent rather than silently identifying two unrelated variables. The new
Round20 source then changes exactly two rows: the stored horizon t0 becomes
2h^2 (actual t=t0+16), and the actual power base becomes t0+16=t instead
of2(t+1). Every other raw row is literally identical. The complete source
array must match the supplied new raw array. Its unbounded justification
is separately accepted in `FACTORIAL_FREE_TPOWER_AUDIT.md`.

For each source the final semantic spherical change is also literal:
remove the budget's constant-1 and change precisely the12(Shared) or11
(factorial-free) normalized-square coefficients from-4 to-2. Every selected
square coordinate must be an actual normalized remainder, or the single
Shared normalized ceiling error. All other terms and rows remain unchanged.
This changes witness existence, not the numerical value of the old guard
or the choice of its nonunique ternary witnesses.

## Monic elimination and exact transformations

Source-stage projection replays each unit-coefficient monic equation,
checks its restoration is independent of its deleted variable, substitutes
it into every row, and verifies the complete live coordinate/row maps and
translation convention. The new checker additionally requires that a
quadratic restoration variable occur only linearly in every other row,
and checks residual degree after every actual substitution. Inherited Horn
factoring is separately checked by the retained independent algebra checker.
The complete common252 finite chain is run as a subprocess, explicitly
propagating optimized mode under-O.

Every subsequent residual-row addition has its explicit subtraction inverse.
Every coordinate shear has pivot1, is linear in other coordinates, and
is checked by substituting its integral inverse into every changed row.
Each projection uses a literal plus/minus monic row and unique integral
restoration of degree<=2. All residual degrees remain<=2 after every step.
Stage compaction is exact live-index renaming. From the244-coordinate
Shared semantic source, the238 and237 endpoints have6 and7 certified
projections respectively; from the245-coordinate power source,239 has6.
The exposed241 and242 companions each have3. No extra free coordinate is
silently discarded after these semantic sources.

All final residual arrays exactly match replay. The complete sum of squares
is independently multiplied out and every coefficient compared with the
supplied expansion. Every coordinate is present. Exact degree, support,
coefficient height and residual height are recomputed, not accepted from
metadata or numerical sampling.

| Endpoint | Variables | Rows | Degree | Support | Height |
|---|---:|---:|---:|---:|---:|
| balanced238 |238|175|4|5236|3968|
| dimension237 |237|174|4|18569|7680|
| power239 |239|175|4|5137|3968|
| exposed241 |241|178|4|4913|170496|
| power_exposed242 |242|178|4|4814|170496|

The last two are legitimate lifting sources with larger height, not claims
that they dominate the other endpoints. The checker imports no producer or
search module. Retained independently authored algebra checkers remain
explicit dependencies. Finite verification establishes the emitted algebra;
it does not independently reprove the unbounded calibration or assert a
new end-to-end formal-kernel consistency theorem.

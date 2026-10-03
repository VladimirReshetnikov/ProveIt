# Independent review of the paid three-mass arithmetic prototype

**PASS on the repaired bounded emitter.** The complete advertised savings are real in the specified circuits: `INC2;DEC2` costs 60→56 for both native and compact-clean endpoints; the three-increment chain costs 116→107 native and 114→105 compact-clean. The prime-three zero test ties its best emitted old schedule at 30 operations. No unconditional improvement over an optimized old evaluator, universal fixed-arity improvement, or globally optimal circuit is established.

Reviewed source SHA-256: `d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0` (`three_mass_arithmetic.py`). Reviewed author receipt: `e13858da0f3385fe25ea719364f8fbf3fe9367893571972fbd3d8d0db82ec203`. I read the entire emitter, verifier and companion proof note, and the original pinned `certificate.py` and `clean_targets.py`; the natural-zero mass-coordinate induction is independently recorded in [the earlier mathematical note](review_three_mass_mass_coordinate_math.md).

## Independent complete-source evidence

The [independent checker](review_three_mass_arithmetic.py) authenticates the candidate before import, then uses its pinned archive loader only to access the original producers and its emitter to obtain the object under review. It does not call the candidate's verifier, polynomial expansion, polynomial evaluator, affine substitution helper or cost checker. Instead it independently constructs all 38 original source/compact-clean fixtures, verifies their complete descriptor digests, substitutes actual step coordinates in their original affine rows and products, and expands every emitted gate with separate exact coefficient arithmetic indexed by coordinates.

The [receipt](review_three_mass_arithmetic.json) records:

- **228** complete emitted-circuit polynomial identities (38 certificates × three coordinate schedules × two inactive-product schedules).
- **1,686** individual affine-residual port identities and **372** complete inactive-step sum identities.
- **13,704** live, topologically closed, paid binary gates, independently recounted by operation.
- **76** matched-schedule checks: exactly `Bh` fewer additions and unchanged multiplication count.
- **12** additional full-source identities with clock scale four, using both actual source compilers.
- Five independently reconstructed valid producer packets outside the bounded emitter interface, all rejected after the repair.

All full sources saved by the author for the six representative fixtures match exactly. Every main expanded output has a nonzero quadratic coefficient, so the reported degree two is exact on those 228 endpoint-bearing circuits. The original source exports, not hand-selected residual subsets, supply the comparison polynomial. No unchanged author suite was rerun.

## Arithmetic and baseline audit

All node operations are explicit binary `+`, `-` or `*`; subtraction counts as one addition. Nonunit fixed coefficient multiplications are emitted and counted. Constant arithmetic and multiplication by zero/one are legitimately folded for the fixed compiler parameters. This is an arithmetic-operation model, not a bit-cost accounting for coefficient size.

The graph computes `N0=x+1` in a live paid register. Its polynomial was independently checked to be precisely `x+1`; subsequent uses of x are rescheduled through that port with the corresponding constant correction. Source-state coefficient groups, every selector/control/mass residual, every requested final mass and physical-time endpoint, each square, each inactive sum and the final addition tree are included in the final polynomial expansion. In particular, the compact-clean time includes `192 N_h`, `192 N_0`, the constant 16 and the doubled forward time; scale four is not omitted. All charged gates reach the output, and every operand resolves to an earlier gate, declared coordinate or exact integer constant.

The fair comparison has four actually emitted old-coordinate schedules: direct sparse-affine or shared-offset coordinates, each with direct or factored inactivity. It takes their minimum before comparing with the two mass-coordinate schedules. The shared-offset schedule already computes `v=e+u`, so its comparison with the new coordinate schedule proves the exact `Bh` saving without treating mass sums as free. The direct sparse-affine baseline can avoid some of those additions, as the zero-test tie demonstrates. The note states this distinction correctly.

For `B>=3`, when both E and the mass sum S are already paid, the direct inactive subcircuit costs `B M+(2B−1) A`; factoring gives `(B+1) M+B A`, a net `B−2` saving. If S is not already available, its `B−1` additions make this factoring one operation worse. The actual emitter pays or shares those sums through its DAG rather than assuming their availability. For `B=2`, the direct factors are the other selectors and need no subtraction; for `B=1`, the inactive polynomial is zero. The actual h=0, B=0, premature-halt and wrong-horizon emitted forms are included in the complete identities, without claiming they have accepting witnesses.

## Resolved prototype-interface finding

The initial draft accepted any apparent free-raw-x certificate, while always recording a paid live N0 port and using fixed internal register names. A valid no-endpoint certificate at h=0 could make the polynomial constant and prune N0, contradicting that port requirement; valid custom output names such as `g0` or `u_7_0` could collide with internal gates or the mass-coordinate renaming.

The author resolved this by explicitly restricting the prototype to precisely its advertised interfaces: natural raw input named `x`, native free final mass/time named `y,T`, or compact-clean free time named `T`. The five valid original-exporter boundary cases are now rejected. All 228 arithmetic schedules and ledgers are unchanged. The note plainly states that `emit`/`evaluate` are internal research algebra routines for freshly generated authenticated certificates, not arbitrary hostile-packet validators or a general hygienic replacement for the source compiler. No broader API guarantee is inferred.

## Mathematical scope retained

The whole polynomial equality is `F_new(x,e,v,...) = F_old(x,e,v−e,...)` as an integer polynomial, not equality on unchanged coordinate values. The independent prior induction establishes natural inverse coordinates on complete natural zeros; the displayed rational decrement/zero-test fixtures correctly show why that result does not extend to the full nonnegative-real domain. The compact-to-full cleaned witness lift remains a zero-fibre theorem rather than an off-zero equality with the larger naïve polynomial.

The branch table and horizon remain external compiler parameters; the core still has `2Bh` natural witnesses. This emitter supports the paid raw interface `N0=x+1` only, not the original producer's bounded-counter loader or arbitrary fixed/renamed endpoints. The raw number's counter valuation interpretation is not an unbounded ordinary-counter input encoder. No unbounded horizon is packed and no global universal-operation bound changes.

## Replay

```sh
python3 review_three_mass_arithmetic.py \
  --source /path/to/three_mass_arithmetic.py \
  --receipt /path/to/three_mass_arithmetic.json \
  --repo /path/to/Proofs \
  --expect review_three_mass_arithmetic.json
```

The checker has explicit path arguments and source/receipt pins, no temporary-worktree dependency, and exact type-sensitive saved-result comparison. Its fresh replay reproduced the full independent receipt. No repository or Git state was modified.

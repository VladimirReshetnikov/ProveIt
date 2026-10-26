# Two further scalar proof simplifications for the thirteen-coordinate carrier

Base commit: `efa64ca941cdae37bb6f7fc5093ae8bb69296ca3`.

## Scope and novelty

These proposals affect `ThirteenCarrierSoundness.auxiliary_estimates`,
`ThirteenCarrierSoundness.transport_nonneg`, and
`ThirteenFreshSeed.carrier_exists`. The exact targets and the two mechanisms
below were checked against the prior proposal corpus by `novelty_audit`.
They are distinct from the earlier Pell sequence envelope estimates, common
negative-norm obstructions, integer-unit extraction, and abstract divisibility
witness recommendations.

The patch intentionally preserves the entire existing proof of `y ≠ 0`
verbatim. That proof could separately use the already-proposed integer-unit
API, but **no saving from that earlier idea is counted here**. The new norm
tail can be transplanted after the prior unit-based refactor without change.
Similarly, the exact witness expression used in the affine construction is
unchanged.

One investigated ratio-divisibility cleanup was rejected and removed because
packet l already proposes keeping divisibility witnesses abstract. Merely
applying that mechanism at `RatioReparameterization.combined_dvd_iff` would
not meet the user's novelty requirement.

## A1. Turn the auxiliary root bound into a positive polynomial certificate

The existing theorem assumes

\[
 S\ge 2,\qquad S^2V^2-(S^2-1)y^2=1
\]

and concludes `y ≠ 0 ∧ |y| < 2 * |V|`. Its current root-bound tail introduces
two contradictions: first to show `y² < 4V²`, then to pass from squares to
absolute values. Both can be replaced by one exact identity:

\[
 (S^2-1)(4V^2-y^2)=(3S^2-4)V^2+1.
\]

The right-hand side is strictly positive because `S² ≥ 4` and `V² ≥ 0`.
The left multiplier `S²−1` is nonnegative, so the second factor must be
strictly positive. The existing library theorem `abs_lt_of_sq_lt_sq` then
transports the strict squared inequality to the desired root bound.

This argument does not assume a sign for `V` or `y`, does not construct a new
Pell solution, and does not require `V ≠ 0` to establish the bound. The
nonzero-ordinate part remains exactly the old proof in the conservative patch.

The replacement tail is:

```lean
  refine ⟨hy, abs_lt_of_sq_lt_sq ?_ (by positivity)⟩
  have hnonneg := mul_nonneg
    (show 0 ≤ 3 * S ^ 2 - 4 by omega) (sq_nonneg V)
  have hprod : 0 < (S ^ 2 - 1) * (4 * V ^ 2 - y ^ 2) := by
    nlinarith only [hn, hnonneg]
  have hlt := pos_of_mul_pos_right hprod
    (show 0 ≤ S ^ 2 - 1 by omega)
  nlinarith only [hlt, sq_abs V]
```

The checked file formats the two helper expressions on single lines;
`auxiliary_estimates` decreases from 28 to 23 physical/nonblank lines,
including its unchanged statement. This five-line incremental saving is
independent of the older unit proposal. The practical benefit is also that
the proof now exposes its one algebraic certificate instead of depending on
two generated contradiction contexts.

The hypothesis `S ≥ 2` remains essential: at `S = 1`, `V = 1`, the norm is
one for every integer `y`, so the root bound is false in general and `y = 0`
is allowed. No guard is silently weakened.

## A2. Share the affine step bound between soundness and completeness

Write

\[
 K=1+bV^2.
\]

The literal carrier equation

\[
 y=1+4\bigl(b(m-V^2G)-G\bigr)
\]

has the equivalent linear shape

\[
 4bm=y-1+4KG.
\]

For a positive integer `b`, a single scalar bound controls both directions:

\[
 2|V|+1<4K.
\]

One transparent certificate for that bound is

\[
 4K-(2|V|+1)
   =(2|V|-1)^2+2|V|+2+4(b-1)V^2.
\]

Every term on the right is nonnegative, and the constant two gives strict
positivity. The fact `b−1 ≥ 0` uses discreteness of the integer domain;
the helper is not asserted for arbitrary positive real `b`.

The new shared helper is only four lines including its statement:

```lean
theorem carrier_step_dominates {b : ℤ} (hb : 0 < b) (V : ℤ) :
    2 * |V| + 1 < 4 * (1 + b * V ^ 2) := by
  have h := mul_nonneg (show 0 ≤ b - 1 by omega) (sq_nonneg V)
  nlinarith [sq_abs V, sq_nonneg (2 * |V| - 1), abs_nonneg V]
```

### Soundness

In `transport_nonneg`, if `G < 0`, integrality gives `G ≤ −1`, hence
`4KG ≤ −4K`. The root bound provides `y < 2|V|`. The normalized right-hand
side `y−1+4KG` would therefore be negative, while `4bm` is positive.
This contradiction proves exactly the existing conclusion `0 ≤ G`.

The argument needs no divisibility hypothesis on `G`; therefore it respects
the current theorem's order in the dependency graph. It does not move
`base_dvd_transport` earlier or assume its conclusion.

The non-strict conclusion must be retained. The assignment
`b=m=1`, `G=0`, `V=3`, `y=5` satisfies the carrier equation and
`|y|<2|V|`; it refutes an attempted strengthening to `0<G` under the
current theorem's hypotheses.

### Completeness

In `carrier_exists`, the existing divisibility hypotheses produce

\[
 G=bg,\qquad y-1=4be.
\]

The witness remains exactly

\[
 m=e+Kg.
\]

The proof derives the normalized equality `4bm=y−1+4KG` once. Since the
theorem assumes `G>0`, integrality gives `G≥1`; the one-sided root estimate
`−2V<y` and `V>0` imply the right-hand side is positive by the shared step
bound. Hence `m>0` because `4b>0`. The same normalized equality closes the
literal witness equation at the end, avoiding a second expansion of `e`
and `g`.

This retains only the original one-sided completeness premise; it does not
invent a stronger two-sided root bound. Both divisibility premises remain
because they construct the actual integral witness, even though they are
unnecessary for the subsequent sign argument.

Here `G>0` also must remain strict. For `b=1`, `G=0`, `V=2`, `y=−3`, all
other premises hold, including `4b | y−1`, but the equation forces `m=−1`.

## Exact source impact

The generated `algebra_metrics.json` is authoritative for counts. The
three replacement declarations are 28→23, 14→9, and 32→20 lines. The new
four-line helper, its documentation, and blank line are charged to the
patch. Across both entire modules the net change is **16 physical lines
removed, 17 nonblank lines removed**. No claim is made about elaboration
speed: the recorded seconds are validation runs, not controlled benchmarks.

All three original theorem headers are unchanged. The only new declaration
is `ThirteenCarrierSoundness.carrier_step_dominates`; the second module
already imports the first, so no import-graph redesign is needed. No
executable definition, polynomial, coordinate layout, witness expression,
or public theorem premise is modified.

## Validation and artifacts

`AlgebraCandidates.lean` contains the exact replacement theorem blocks and
helper under an isolated namespace. It compiles using Lean 4.32.0 with the
installed mathlib cache. All four printed axiom sets are exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.
The final command output and exact candidate SHA-256 are recorded in
`algebra_standalone_compile.log` and `algebra_compile_result.json`.

`build_algebra_patches.py` creates the proof-only two-module overlay and
unified patch, verifies all original theorem headers, verifies that the
nonzero-ordinate prefix is unchanged, and records source/overlay hashes.
This is targeted proof elaboration, **not a claimed full repository build**.
Before merging, rebuild `ThirteenCarrierSoundness`, `ThirteenFreshSeed`,
their existing Checks modules, and their direct clients against the exact
maintained dependency tree. The accompanying candidate contains no guessed
repository API names beyond the new shared helper.

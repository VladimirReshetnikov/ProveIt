# Three local simplifications in the new controller proof chain

Reviewed ProveIt commit: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.
These are concrete applications of existing Mathlib theorems in newly added
controller modules. They are not a new modular-arithmetic framework.
The independent novelty reviewer found no earlier proposal for these exact
three targets in the 23 placed packets and five incoming archives. Earlier
cyclic-word cast interfaces address different obligations. Broad advice to
reuse library results is not itself claimed as new.

## C1. Compare bounded representatives directly

Target: `ControllerIntervalSums.interval_injOn`, source line 25.
The original six-line body establishes bounds for `j` and `k`, cancels the
common translation, applies `ZMod.val`, and simplifies both remainders.
The replacement is the three-line body:

```lean
  intro j hj k hk he
  exact ((ZMod.natCast_eq_natCast_iff j k T).mp (add_left_cancel he)).eq_of_lt_of_lt
    ((Finset.mem_range.mp hj).trans_le ha) ((Finset.mem_range.mp hk).trans_le ha)
```

The mathematical fact is precisely uniqueness of a representative below the
modulus. `a ≤ T` supplies both bounds. The translation still cancels before
comparison, so a wrapped interval is handled exactly as before. `T = 1`,
the empty interval `a = 0`, and the full interval `a = T` remain valid.
The theorem header, hypotheses, definition of `interval`, and every caller
are unchanged. Net saving: three physical source lines.

## C2. Normalize the quotient projection before taking its value

Target: `ControllerResidueLift.exists_coordinate`, source line 20.
The old proof reconstructs the library fact that the projection
`ZMod (C0*T) → ZMod C0` sends an element to its canonical natural value
reduced modulo `C0`. It introduces `phi`, rewrites the source element as
`z.val`, and invokes preservation of natural casts. The library already
exposes this normalization as `ZMod.castHom_apply` and `ZMod.cast_eq_val`.

```lean
  have hm : z.val % C0 = a := by
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      Nat.mod_eq_of_lt ha] using congrArg ZMod.val hz
```

The existing quotient witness `(z.val / C0 : ZMod T)`, its strict bound,
and the final `Nat.mod_add_div` identity are preserved byte for byte.
Neither `C0` nor `T` is assumed prime; the same-prime case, where a CRT
argument would be invalid, remains covered. `T = 1` forces the quotient
coordinate to zero as before. `C0 = 1` forces `a = 0` and is also retained.
Net saving: five physical source lines.

## C3. Use the semantic nonzero and positive-value interfaces

Target: `ControllerAuxiliaryChoice.exists_coprime_cardinality`, line 27.
The Boolean choice already supplies `phi r ≠ 0`. The original proof builds
an auxiliary cast equality, manually contradicts divisibility, then starts
another arithmetic contradiction to show `0 < r.val`. The replacements are:

```lean
  have hnd : ¬ p ∣ r.val := by
    apply (ZMod.natCast_eq_zero_iff r.val p).not.mp
    simpa only [phi, ZMod.castHom_apply, ZMod.cast_eq_val] using hr
  have hpos : 0 < r.val :=
    ZMod.val_pos.mpr (fun hz => hr (by rw [hz, map_zero]))
```

The positivity argument uses only that a homomorphism sends zero to zero:
`phi r ≠ 0` implies `r ≠ 0`, hence its least representative is positive.
Primality is used at the same final step as before to obtain coprimality
with `p^n`. Composite `C0`, exponent `n = 0`, both Boolean choices, and
the unchanged `0 < a < C0` conclusion all remain covered. Net saving:
five physical source lines.

## Measurements and validation

The three changed production modules contain 201 physical lines before and
188 after, a net reduction of 13. The unchanged intervening
`ControllerOrbitTransport` has 108 lines. All four together go from 309 to
296 lines. There are no new helpers, changed theorem types, added axioms,
or altered definitions. The patch preserves all original imports.

The exact patch passes `git apply --check` at the pinned checkout. The
original and proposed standalone proofs were compiled with Lean 4.32.0 and
the repository-pinned Mathlib. Both old and new versions have these axiom
footprints:

| Theorem | Axioms |
|---|---|
| `interval_injOn` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_coordinate` | `propext`, `Quot.sound` |
| `exists_coprime_cardinality` | `propext`, `Classical.choice`, `Quot.sound` |

The complete modified four-module chain was also compiled in dependency
order in a separate overlay. To use a bounded dependency cache, its
validation-only `ControllerIntervalSums` import replaces the umbrella
`Mathlib.Tactic` import by `Mathlib.Algebra.BigOperators.Ring.Finset`.
All four complete semantic modules compile with no body adaptations.
For the original Checks clients, the validation overlay adds
the narrower `Mathlib.Tactic.NormNum` import explicitly. This import
adaptation is not included in the production patch and contributes no
claimed source saving. The original Checks clients and extra boundary
checks all pass (nine successful compiler invocations in the final portable replay),
recorded in `controller-validation.json` and `controller-checks.json`. This is an isolated source
and client replay, not a rebuild of the entire ProveIt repository. Recorded
seconds are replay durations, not evidence of a performance improvement.

## Files

- `controller-cast-normalization.patch`: three production proof-body edits.
- `controller_sources/before/`: exact original four source modules.
- `controller_sources/after/`: proposed four modules with original imports.
- `controller_overlay/`: complete minimal-import validation sources and checks.
- `ControllerCastReview.lean`, `ControllerCastBaseline.lean`: source-shaped
  proofs and old/new axiom checks.
- `ControllerIntervalBaseline.lean`: original interval proof axiom check.
- `controller-metrics.json`: full-file line counts and SHA-256 values.
- `controller-compile.json`, `controller-checks.json`, `controller-validation.json`: final successful compiler receipts.
- `controller-replay.py`: portable nine-invocation replay; takes `--mathlib-root` and `--lean-bin`.
- `independent_order_controller_review.md`: independent statement and
  boundary review, plus independently compiled controller proofs.

## Why not add a larger abstraction here?

A general equivalence between the projection fiber and `ZMod T` is
mathematically natural. Its implementation would add proof and interface
code to replace one already short witness construction. No present net
saving has been demonstrated, so it is not included as a recommendation.
Likewise, a whole-kernel reduction modulo two would repeat too much of the
previous scalar projection and carry-parity proposals; it is excluded.

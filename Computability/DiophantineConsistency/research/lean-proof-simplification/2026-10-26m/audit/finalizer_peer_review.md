# Independent review of the finalizer and signed-congruence proposals

Snapshot: `7fa06d530df54d4aeb2e18027409df082234c69e`.
Reviewed proposed files are under `proposed/Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
This note distinguishes source comparison and mathematical review from the root agent's compilation receipts.

## Finalizer refactor: sound mathematical boundary

The new lemma

```lean
theorem rat_intCast_num_of_pow {q : ℚ} {z : ℤ} {n : ℕ}
    (hn : n ≠ 0) (h : q ^ n = (z : ℚ)) : (q.num : ℚ) = q
```

preserves the actual signed rational root. Applying `Rat.den` to the power equation forces the denominator of `q` to be one: the denominator of an integer is one, the reduced denominator of a rational power is the corresponding natural power, and a nonzero natural exponent cannot make a denominator greater than one equal to one. The final numerator-cast equality therefore reconstructs `q`, including its sign. The `n ≠ 0` premise is necessary: `q^0=1` holds for nonintegral rationals.

This is stronger information for the consumer than merely obtaining `IsSquare a`. The old finalizer proof discarded the rational root, chose an arbitrary integral square root, and recovered the correct sign by a two-by-two case analysis. Keeping `r.num` and `s.num` preserves the original linear identity `theta/omega = r + w*s`. Casting that identity back to integers then needs one proof branch.

The separated norm theorem moved into the foundational finalizer is mathematically identical in statement to the existing Margin finalizer theorem. Its three nondegeneracy conditions remain essential:

- `omega ≠ 0` prevents the norm equation from losing all radicand information.
- `w ≠ 0` makes the second rational root reconstructible.
- `a ≠ w^2*b` rules out the `theta=0` degeneration, which can occur even with nonsquare radicands (for example `a=b=2`, `w=omega=1`, `theta=0`).

The bounded-radicand theorem still retains all its original premises. With `b>0` integral, `b≥1`; hence `w²*b≥w²>a`, proving the separation required by the generalized theorem. No positivity or square-root assumption has been silently added.

## Compatibility and complete source accounting

Source comparison found every pre-existing public declaration header unchanged and no removed declarations. The only new public declarations are `NearSquareFinalizer.rat_intCast_num_of_pow` and `NearSquareFinalizer.integer_roots_of_separated_norm_zero`. `MarginFinalizer.integer_roots_of_separated_norm_zero` keeps its exact original statement and becomes a qualified wrapper. All imports are unchanged.

The bodies of `NearSquareFinalizer.norm`, `NearSquareFinalizer.value`, and `MarginFinalizer.value` are identical to the original source. Thus this edit changes proof organization and existential proof witnesses, not polynomial definitions, executable arithmetic, degrees, coefficients, or counted data. `finalizer_static_review.json` records old/new hashes, header comparisons, and data-body comparisons.

| File | Before | After | Saving |
|---|---:|---:|---:|
| `NearSquareFinalizer.lean` | 255 physical lines | 251 physical lines | 4 |
| `MarginFinalizer.lean` | 177 physical lines | 135 physical lines | 42 |
| Total | 432 | 386 | 46 |

The byte totals are 19,847 before and 17,175 after, a reduction of 2,672 UTF-8 bytes. These totals charge both new helper declarations, the specialization proof, the compatibility wrapper, comments, and blank lines. The two original root-recovery declarations occupied 97 lines; their replacements plus new helper declarations occupy 48 declaration lines. That 49-line local reduction must not replace the honest 46-line whole-module figure.

One migration bug was independently found and repaired by the root agent: the new nonzero `hw` premise cannot be passed to `ne_of_gt`. Its rational cast now uses `exact_mod_cast hw`. Separate rewrites for the two root equations avoid rewriting irrelevant subterms. The root agent owns the final full-module compiler receipts; the standalone rational helper has a recorded zero exit status and standard axiom set `[propext, Classical.choice, Quot.sound]`.

Moving the separated theorem downward introduces no import cycle: Margin already imports NearSquare. An occurrence search found no maintained source that opens both finalizer namespaces. The added basename is therefore not an observed ambiguity in the current tree, although qualified names are appropriate in future clients. Recompiling Margin against the changed NearSquare artifact, plus their existing check modules, is the direct integration check that matters.

## Novelty relative to the submitted packets

The seven current incoming ZIPs and the placed packet referenced by the incoming README contain no identified rational-root integrality/descent or finalizer-deduplication proposal. Their references to `NearSquareFinalizer.norm` concern extraction of the common Split/Gap scalar tail, not the signed root reconstruction proof. Their sum-of-squares suggestions concern residual aggregation, a different argument. This is a new source-specific refactor relative to that inspected corpus; neither denominator integrality nor the separated norm theorem is claimed as new mathematics.

## Signed modular composition: recommended interface

Keep the relation explicit over arbitrary integers:

```lean
abbrev SignedModEq (m a b : ℤ) : Prop :=
  a ≡ b [ZMOD m] ∨ a ≡ -b [ZMOD m]

theorem SignedModEq.symm
    (h : SignedModEq m a b) : SignedModEq m b a

theorem SignedModEq.trans
    (hab : SignedModEq m a b) (hbc : SignedModEq m b c) :
    SignedModEq m a c

theorem SignedModEq.of_sign_mul
    (h : a ≡ ε*b [ZMOD m]) (hε : ε=1 ∨ ε=-1) :
    SignedModEq m a b

theorem SignedModEq.iff_dvd_sub_or_add :
    SignedModEq m a b ↔ m ∣ a-b ∨ m ∣ a+b
```

The root agent's `experiments/signs/SignedModEq.lean` implements these statements and `compose_residues`, with a recorded successful compiler result. The four transitivity cases use only ordinary modular transitivity and negation; individual divisibility quotients disappear. The bridge handles the orientation of `Int.modEq_iff_dvd` explicitly (`m ∣ b-a`), avoiding a common sign mistake.

In `NativePellStepDown.index_residues`, compose:

1. `hu_J`, reversed: `J` is congruent to `u` up to sign.
2. `hu_cc` and `neg_one_pow_eq_or`: `u` is congruent to `s` up to sign.
3. `hsp'`, converted using the divisibility bridge: `s` is congruent to `p` up to sign.

The existing `hJs` and `hJp_of_sign` blocks can then be replaced by one application of the composition theorem. This is precisely the repeated mathematical argument, rather than a tactic that reproduces the four quotient-witness constructions invisibly.

No positivity assumption on the modulus is needed. At `m=0`, the relation reduces to equality up to sign and remains transitive. For negative `m`, divisibility and modular equivalence have the same meaning as for `-m`. The proposed statements quantify over every integer modulus and do not divide by it. Zero roots and coincident positive/negative branches need no special cases. Keep the API over integers; replacing it with natural-number congruence would lose the negative representatives used here.

## Odd Pell index reuse and integration risks

`SignedPellResidue.odd_index_of_base_dvd` already proves the oddness required in `index_residues`. A suitable application is:

```lean
have hsodd : Odd s :=
  SignedPellResidue.odd_index_of_base_dvd hI1 (by
    rw [← hIu]
    exact dvd_mul_right I u)
```

The additional module imports only `Diophantine.Common.PellInt`, so the proposed reuse does not create a dependency cycle. The natural Pell parameter and its `1<I` proof are the same at this call site. The original `hs0` fact is unused anywhere in the remainder of `index_residues`; it can be deleted while retaining the public `hy` premise unchanged for compatibility.

Charge the signed-congruence helper module and new imports against the final line count. The local quotient-case saving by itself is not the net package saving. Check the complete modified step-down module and its source-index endpoints, not only the portable relation. Axiom audits should be compared per affected theorem. The previously submitted Pell refactor concerned only `eq_of_residues` casts, so this odd-index reuse and sign-relation composition are distinct proposals. Source-row decoding in earlier packets is also a separate interface.

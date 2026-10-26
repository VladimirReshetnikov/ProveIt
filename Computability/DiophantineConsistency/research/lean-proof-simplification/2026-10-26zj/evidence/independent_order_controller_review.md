# Independent review: finite-order rigidity and controller cast proofs

Reviewer: semantic_simplifications agent, independent of the two patch authors.
Base repository commit: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.
Reviewed file hashes are in `independent_order_controller_hashes.json`.

## Finite-order rigidity: accepted

The standalone theorem has exactly the production contract

    {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f) (i : Fin n) : f i = i.

The library `OrderHom.eq_id_of_injective`, at pinned mathlib `Mathlib/Data/Finset/Sort.lean:389`, assumes a finite linearly ordered type and an injective monotone self-map. Strict monotonicity supplies both monotonicity and injectivity. Applying equality of bundled functions to `i` yields exactly the desired equality.

This is a proof of finite-chain rigidity. It does not need a distinguished least point, an assumption `0 < n`, an explicit surjectivity witness, or the custom strong induction. The empty finite ordinal is handled vacuously; the singleton case remains valid. The generic finite-linear-order extension in the standalone file is correct. It must not be generalized to arbitrary partial orders: incomparable points may be exchanged by an order automorphism.

The change is confined to the generic rigidity lemma. It still requires the actual client theorem `rankMap_strictMono`, so it does not certify literal tile ordering or remove the physical-order data obligations.

Independent command:

    lake env lean /workspace/scratch/32e993da5b34/analysis/FiniteOrderRigidity.lean

Result: exit 0. Axiom output:

    'ProveItReview.strictMono_fin_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ProveItReview.strictMono_finite_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]

At review time the exact production patch had not yet been supplied; the standalone proof and the production statement were compared directly. No full physical-order dependency rebuild is asserted by this review.

## Controller source patch: accepted

`controller-cast-normalization.patch` changes only proof bodies in three modules. The theorem declarations, variable binders, typeclass hypotheses, witness statements and computational data are unchanged.

### `ControllerIntervalSums.interval_injOn`

After canceling the common translation, equality in `ZMod T` becomes `Nat.ModEq T j k`. The existing range bounds give `j < T` and `k < T`, so the standard uniqueness theorem for reduced representatives gives equality.

The proof retains `a ≤ T` and `[NeZero T]`. It handles `a = 0`, `a = T`, modulus one, and composite moduli. It does not replace bounded representatives with an unrestricted injectivity claim about the natural-number cast.

An independent standalone `ControllerIntervalIndependent.lean` contains the exact proof and instances for an empty interval, a full interval at composite modulus six, and modulus one. It compiled successfully and reports only `[propext, Classical.choice, Quot.sound]`.

### `ControllerAuxiliaryChoice.exists_coprime_cardinality`

For `r = t - e*b`, the already-proved fact `phi r ≠ 0` is converted directly to nondivisibility of the representative `r.val` by `p`. This follows from `ZMod.castHom_apply`, `ZMod.cast_eq_val`, and `ZMod.natCast_eq_zero_iff`; the source modulus remains nonzero.

Positivity is proved independently of primality: if `r = 0`, the homomorphism sends it to zero, contradicting `phi r ≠ 0`; then `ZMod.val_pos` gives `0 < r.val`. The old proof obtained the same positivity indirectly from nondivisibility.

The proof still requires primality only for coprimality with powers of `p`, still permits composite `C0`, and retains exponent `n = 0`. It does not assume that the controller modulus is prime or that the exponent is positive. The impossible `C0 = 1` plus prime-divisor hypotheses do not introduce a hidden case exclusion.

### `ControllerResidueLift.exists_coordinate`

The original projection equality is normalized directly to `z.val % C0 = a`; no auxiliary `phi` and representative transport equality are needed. The premise `a < C0` is essential and retained. The quotient bound, coordinate witness and `Nat.mod_add_div` reconstruction remain unchanged.

Both `[NeZero C0]` and `[NeZero T]` are preserved. At `T = 1`, the canonical quotient is zero because `z.val < C0`; at `C0 = 1`, `a < C0` forces `a = 0` and the construction remains valid. No division or unit inverse in the modular ring is introduced.

Independent command:

    lake env lean /workspace/scratch/32e993da5b34/analysis/ControllerCastReview.lean

Result: exit 0. Axiom output:

    'ControllerCastReview.exists_coordinate' depends on axioms: [propext, Quot.sound]
    'ControllerCastReview.exists_coprime_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound]

Independent command:

    lake env lean /workspace/scratch/32e993da5b34/analysis/ControllerIntervalIndependent.lean

Result: exit 0. Axiom output:

    'IndependentControllerReview.interval_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]

These are exact standalone theorem checks. Production-module validation, if subsequently completed by the author, should be reported separately; this review does not infer it from the standalone checks.

# Two residual Pell proof simplifications

Repository pin: `96520cd1a5179f470b4da127bd47bc26a8d808ff`.
The two patches change only proof bodies, add no declarations or imports, and preserve every public theorem statement.

## 1. Normalize the existing squared norm at the classifier boundary

Target: `SignedPellResidue.signed_residue_cases`, original lines 62–67.
The existing hypothesis `hn` already says

`(A * V.natAbs)^2 = (A*A - 1) * y.natAbs^2 + 1`.

Use the natural subtraction equation supplied by `Nat.sub_eq_of_eq_add'` directly as the input of `Pell.eq_pell`:

```lean
  obtain ⟨n, hx, hy⟩ := Pell.eq_pell hA (x := A * V.natAbs) (y := y.natAbs) (by
    change (A * V.natAbs) * (A * V.natAbs) - (A * A - 1) * y.natAbs * y.natAbs = 1
    simpa only [pow_two, mul_assoc] using Nat.sub_eq_of_eq_add' hn)
```

The explicit `change` is required in this exact Lean version: the theorem's expected type retains Mathlib's private Pell discriminant, which the restricted `simpa` alone does not unfold. The primed natural-subtraction lemma is the correct orientation. This removes both an intermediate product-form equality and the subsequent `omega` proof. The module changes from 102 to 99 physical lines, counting comments and blank lines.

This is separate from the k/m signed congruence and natAbs-output refactors, which operate after classification. It also leaves the already-proposed odd-index theorem reuse alone. Using `Jones1980.eq_pell_of_sq` was considered and rejected because it would require an extra import here; the delivered replacement needs only existing dependencies.

## 2. Obtain integer Pell norms from the existing integer norm theorem

Target: `ThirteenFreshSeed.auxiliary_exists`, the `hp` and `hnorm` blocks at original lines 105 and 140. Mathlib already exposes `Pell.pell_eqz`; `Pell.dz_val` expresses its discriminant as the expected integer polynomial. The current proof derives both identities afresh by casting `χ_sq` from natural numbers and discharging truncated-subtraction cast guards.

The first norm becomes:

```lean
  have hp : f ^ 2 - delta * (yn hA t : ℤ) ^ 2 = 1 := by
    simpa only [f, delta, xz, yz, dz_val, az, pow_two, mul_assoc] using pell_eqz hA t
```

The second norm uses the already-established equation `hx` for the first coordinate and the existing negative second coordinate `y`:

```lean
  have hnorm : (S : ℤ) ^ 2 * V ^ 2 - ((S : ℤ) ^ 2 - 1) * y ^ 2 = 1 := by
    have h := pell_eqz hS R
    simp only [xz, yz, dz_val, az, hx] at h
    dsimp [y]
    nlinarith only [h]
```

The module changes from 217 to 210 physical lines. The `hAA` guard remains because the distinct `hSz` cast still needs it. No positivity or sign assumption is dropped.

Nearest prior work differs in its exact obligation. Packet l's integer norm proposal proves `MinimumNorm.norm_ne_zero_of_not_isSquare` by integer divisibility and square cancellation. Here the norm equals one by a theorem about the already-constructed Pell sequence. Packets ze/zk simplify `carrier_exists` and the soundness transport, while these replacements lie in `auxiliary_exists`. The auxiliary norm estimates themselves are unchanged. Searches of the proposal prose found no `pell_eqz`/`dz_val` reuse proposal; source-level comparisons, not token absence alone, justify the distinction.

## Verification and artifact meanings

Both `*Audit.lean` files are the complete modified current source module followed by `#print axioms` commands for the modified theorem and its public downstream endpoint. Both compiled successfully using Lean 4.32.0, commit `8c9756b`, against existing baseline dependency objects. Each endpoint reports exactly `propext`, `Classical.choice`, and `Quot.sound`; neither check reports `sorryAx`. This is a complete-module check against cached dependencies, not a clean whole-project rebuild or a simultaneous build of all assumed prior proposals. Direct import source files match the pinned Git tree, as recorded in the manifests. No compilation-speed claim is made.

- `*.original.lean`: exact original current source.
- `*.lean`: modified complete source; `*Audit.lean` additionally contains axiom audit commands.
- `*.patch`: reviewable unified diff against the pinned repository path.
- `*.lean.log`: final successful compiler output.
- `*.validation.json`: exit status, exact checked SHA256, timing, and declared check scope.
- `*.manifest.json`: original/modified hashes, physical line counts, and pinned/cache direct-import correspondence.

All line savings are measured against the literal pinned checkout. They describe these residual edits; they are not totals for the hypothetical tree after all older proposals have been applied.

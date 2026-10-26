# Digit, carry, and current-cell proof simplifications

Reviewed snapshot: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
All source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
No original repository source was changed. The proposals preserve the existing
mathematical boundaries: sparse support is not occupation, at-most-one is not
exactly-one, and phase recovery must not be used as its own premise.

## Checked deliverables

`HalfShiftArithmetic.lean` and `NormalizationArithmetic.lean` compile under
Lean 4.32.0 with `import Std.Tactic`, without Mathlib or repository imports.
The corresponding `.check.log` files record successful `#print axioms` output.
Across their six theorems, the only axioms reported are `propext` and
`Quot.sound`. No `sorryAx`, native decision axiom, or extra source axiom occurs.
These are checked reusable arithmetic lemmas. The wrappers in the original
project and the separate candidate patches require project-level compilation;
do not describe every proposed integration as checked on this evidence alone.

## 1. Put a conditional witness inside the branch that needs it

**Priority: high; small API change with a concrete two-file patch.**

`NativePreliminaryCount2011.total_le_one_all_phases` (lines 61--87) receives
`u : Nat -> Nat` globally, even though `u` is used only in the middle-phase
branch `7 <= phase <= 10`. The literal caller in
`CurrentCount2011.count_le_one_of_middle_padding` (lines 32--64) consequently
manufactures a global `u` by a case split (lines 46--54): it extracts the real
padding witness in the middle branch and chooses a dummy zero function outside
that branch.

Change the generic theorem to accept

```lean
(hpadding : 7 ≤ phase → phase ≤ 10 → ∃ u : ℕ → ℕ,
  ... u ...)
```

and destruct `u` only after entering the middle branch. Then the caller can
pass its existing `hpadding` directly; the entire dummy-witness block and its
local `classical` disappear. The logical strength of the actual application is
unchanged: no additional padding premise is introduced. In fact the generic
API expresses its genuinely conditional data dependency more accurately.

`conditional-padding.patch` implements this change against the exact snapshot.
The two original files total 155 physical lines; the proposed files total 145.
The core theorem's line count stays 89, while the caller changes from 66 to 56.
`ConditionalPadding.lean` gives the proposed generic theorem under a fresh name,
so it can be tested without replacing the original theorem. The patched caller
still needs compilation with the changed generic theorem. Repository search
found one production call of `total_le_one_all_phases`, plus a `#print axioms`
check and documentation references. If an external user needs the old API,
retain it temporarily as a short wrapper that supplies `⟨u, hpadding ...⟩`;
that compatibility option has a different source-line total.

## 2. Use the existing stronger congruence at smaller moduli

**Priority: high; six lines saved in one proof body without new mathematics.**

`CurrentClause2011.reflected_weight_mod` (lines 122--130) already classifies
every reflected coefficient modulo 2048. `CurrentEarlyPadding2011` repeats
the same five-way constructor split and finite label-position case checks in
its private `reflected_mod_sixteen` (lines 99--107).

Since 16 divides 2048, use

```lean
exact (CurrentClause2011.reflected_weight_mod e).of_dvd
  (by decide : 16 ∣ 2048)
```

The local `selectorUnit` definitions have identical equations, so this proposal
uses definitional equality and does not require making the older private
definition public. A small shared public definition would also work, but is
not necessary for this patch. The old proof body has seven physical lines; the
replacement has one. `modulus-reuse.patch` and `ModulusReuse.lean` provide the
exact patch and a standalone candidate theorem. At the time of this note's
initial preparation, this integration has not been compiled because it needs
the full `CurrentClause2011` dependency chain.

The same principle suggests proving coefficient residues once at the largest
relevant power of two, then using `Nat.ModEq.of_dvd` for lower phases. This
avoids independently maintained finite classifications. It does not justify
discarding higher coefficients, collisions, or carries from the actual word.

## 3. Normalize exact digit/carry equations through a small scalar API

**Priority: high; generic arithmetic helpers compiled.**

Repeated proofs start from

```lean
raw = digit + radix * carry
```

and then recover either a quotient, a residue, or a carry reset. Examples:

- `CurrentClause2011.normalized_clause_residue`, lines 160--166: residue modulo
  2048, using divisibility of the radix.
- `CurrentEarlyPadding2011.padding_digit_residue`, lines 251--258: the same
  arithmetic modulo 16.
- `CurrentPhaseParity2011.marker_digit_parity`, lines 113--117: modulo 2.
- `CurrentEarlyPadding2011.early_carry_zero`, lines 88--93: the raw budget
  lies below one radix, so the outgoing carry vanishes.

The checked `NormalizationArithmetic.lean` proves:

```lean
quotient_of_decomposition
  (hd : digit < radix) (h : raw = digit + radix * carry) :
  carry = raw / radix

residue_of_decomposition
  (hm : modulus ∣ radix) (h : raw = digit + radix * carry) :
  digit % modulus = raw % modulus

zero_carry_of_decomposition
  (hsmall : raw < radix) (h : raw = digit + radix * carry) :
  carry = 0
```

This separates the genuine problem-specific work (the raw coefficient budget,
the reflected residue, or support exclusion) from boilerplate natural-number
division. The residue helper needs no digit bound; the quotient helper does.
The zero-carry helper needs no independently supplied digit bound, because the
small raw total and nonnegativity already give it.

There is also a record-level simplification. `CurrentPolynomialWindow2011.Facts`
already exists and should be retained, rather than replaced by another giant
bundle. Its `carry_recurrence` field (lines 60--62) follows from `digit_bound`
(59) and `carry_equation` (63--66). After adding the generic helper, make
`Facts.carry_recurrence` a derived theorem with the same dot-notation API.
Consumers can keep calling `h.carry_recurrence`; constructors no longer carry
two proofs of the same normalization. Do not remove recurrence from other
interfaces that do not supply a strict digit bound: the equation alone does
not imply the quotient recurrence.

## 4. Replace half-radix case enumeration by an exact quotient/remainder formula

**Priority: medium-high; arithmetic kernel compiled, source integration pending.**

`NativeCyclicRotation.shiftDigits_half_bound` (lines 100--116) splits the current
digit into four cases, then separately bounds the predecessor quotient.
`shiftDigits_half_parity_89` (lines 160--165) enumerates all 16 current/predecessor
combinations. The exact formula is shorter and exposes why both facts hold:

\[
 (sa)\bmod(2s)+\lfloor sb/(2s)\rfloor
   =s(a\bmod2)+\lfloor b/2\rfloor,\qquad s>0.
\]

The checked `HalfShiftArithmetic.lean` derives this using
`Nat.mul_mod_mul_left` and `Nat.mul_div_mul_left`, then proves both the bound
and parity statement. The bound even needs only `b <= 3`; the current digit
`a` can be arbitrary. For parity, also require `s % 2 = 0`. To recover the
existing 89-bit lemma, instantiate `s = 2^88`, use `2^89 = 2 * 2^88`, and unfold
`shiftDigits`. The cyclic predecessor stays exactly `k - 1`. No boundary digit
or half-phase is silently discarded.

This is preferable to replacing the 16 cases with opaque automation: the new
formula supports future radix changes and makes the carry contribution visible.
`NativeBooleanRotation.rotation_eq_scaled` already supplies the corresponding
Boolean no-overflow theorem; do not duplicate or replace it with the weaker
three-valued half-radix bound.

## 5. Put field-coordinate and off-origin mask lemmas below the clause layer

**Priority: medium; architectural proposal, not yet implemented.**

The source repeats two steps: compute the field residue of an aligned cell plus
an offset, then prove the point cannot be the global origin before using the
high-mask lookup.

- `CurrentClause2011.clause_target_residue` / `clause_mask`: lines 41--54.
- `CurrentPhaseParity2011.marker_target_residue` / `marker_mask`: 27--41.
- `CurrentEarlyPadding2011.padding_target_residue` / `padding_mask`: 263--281.

Introduce a shared lemma for `b.val % 2011 = 0` and `e < 2011`:

```lean
(b + (e : ZMod (N * 2011))).val % 2011 = e
```

and a high-mask specialization for `0 < e`:

```lean
maskDigits (b + (e : ZMod (N * 2011))) = cellDigit e
```

The three masks become a shared lookup plus `cellDigit_clause`,
`cellDigit_marker`, or `cellDigit_padding`. A generic source-offset residue
lemma also replaces the parallel `he`, `h18`, `h2020` derivations in
`clause_convolution` (65--90) and `marker_convolution` (51--76).

The dependency placement is essential: `CurrentCellTranslation2011` currently
imports `CurrentClause2011`, so importing its existing `source_residue` into the
clause module would create a cycle. Move only the low-level residue/coordinate
definitions into a small upstream module; keep decoding and coefficient data
above it. `source_residue` already handles arbitrary temporal shifts and both
wrap regimes, so reuse its mathematics. Do not add an artificial `t < N*2011`
restriction. Retain the nonzero full cyclic modulus, the distinction between
natural and group subtraction, the off-origin condition, and the `N = 1` case.

## 6. Share the origin-decrement word lemma across the two high-mask families

**Priority: medium; concrete mathematical interface, not yet compiled.**

`CurrentHighDigits2011.high_mask_word` (107--126) and
`NativeHighPort54.mask_word` (182--202) independently prove that subtracting one
from the origin digit subtracts one from the whole word, with no borrow into a
neighbor. Abstract this part as

```lean
theorem word_sub_origin (r delta : ℕ) (a : ZMod n → ℕ)
    (hdelta : delta ≤ a 0) :
    word r (fun k => a k - if k = 0 then delta else 0) =
      word r a - delta
```

Prove the pointwise additive reconstruction using `Nat.sub_add_cancel`, then
apply `word_add` and the already-existing `word_origin`. Each concrete high-mask
proof is then its existing periodic-word identity plus this helper. This
keeps the no-borrow hypothesis explicit. It must not be generalized to arbitrary
pointwise subtraction without proving the corresponding pointwise bounds.
The source already has `word_origin`, `word_add`, `word_periodic`, and
`periodic_factor`; the proposal fills the small missing composition rather than
reproving those existing abstractions.

## 7. Expose the already-proved physical sum identity directly

**Priority: medium; small API improvement.**

`CurrentClause2011.selectorCount_eq_prefix` (110--116) first proves

```lean
selectorCount c b = ∑ p : Fin 942, c (b + (p.val : ZMod (N * 2011)))
```

using the actual `physicalEquiv`, then converts to a natural prefix sum. Make
that first equality a public named lemma too. `CurrentOneHot2011` (68--71) and
`CurrentFieldOffsets2011` (88--93) currently travel through the prefix-sum form
and back to the `Fin` sum. They can use the direct equality with `simpa only`.
This is not a proposal to assume an arbitrary sorting permutation: the
authoritative `physicalEquiv` and its proof remain the basis of the theorem.
Choose one rewrite direction and avoid adding both directions to the global
simp set.

## 8. Factor the restored canonical window once, preserving its witness

**Priority: medium-long term; shared interface proposal.**

`CurrentSparseDigits2011.polynomial_zero_reconstructs` (118--129) and
`CurrentHighDigits2011.polynomial_zero_mask_test` (141--152) repeat evaluation
conversion, the Carrier65-to-Carrier66 restore, canonical-window extraction,
and the same power normalization. A lower-level lemma in
`CurrentCarrierArithmetic2011` or a new upstream source-window module can
produce the restored source, one positive `N`, and both low/high arithmetic
mask tests. The Boolean and high-digit modules then specialize it.

The important issue is witness coherence, not just shorter text. Downstream
composition must use the same restored source and same `N`; independently
combining two existential statements requires a uniqueness argument.
`CurrentPolynomialWindow2011.polynomial_zero_window` already constructs a
coherent source and window (78--152). Preserve that success and extract only
the genuinely duplicated lower-level portion. Do not replace this by a
package containing desired future tile occupation or machine semantics.

## What to leave alone

- `CurrentHighDigits2011.cellDigit_formula` already proves a symbolic ten-block
  formula instead of 2011 separate digit cases. It is a good abstraction.
- `NativeCyclicCarry.exists_bounded_carries` already uses a monotone fixed point
  on a bounded carry box, so no cyclic starting point is assumed. Its proof is
  short; replacing it with a handwritten iteration would add complexity.
- `NativeFieldCycles2011.offset19_excludes_510` explicitly preserves the real
  511 self-loop. Do not strengthen it to exclude every nonzero cycle.
- Avoid changing all `Nat` arithmetic to `Int` or `ZMod` at once. Truncated
  subtraction and the strict word bound carry actual semantics here.
- Avoid claiming faster elaboration merely from fewer lines. Time both versions
  under the same pinned toolchain, imports, and heartbeat settings before making
  a performance claim.

## Final validation status

Both candidate patches passed `git apply --check` against the pinned snapshot.
The two standalone core/Std modules compiled successfully, with all six theorem
axiom inventories retained in their logs. The direct compilation of the
unchanged `PaddingStaircase` dependency was stopped after prolonged disk/page
waits. Therefore `ConditionalPadding.lean`, `ModulusReuse.lean`, both proposed
source copies, and both integration patches remain **uncompiled**. This is an
incomplete environment-limited project check, not a proof failure. No
repository-wide build or integration success is claimed. `validation.json`
records these statuses in machine-readable form.

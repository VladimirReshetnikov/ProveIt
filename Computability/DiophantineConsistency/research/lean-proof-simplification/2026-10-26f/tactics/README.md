# Local simplification review — UNCOMPILED CANDIDATES

Pinned ProveIt commit: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
Pinned Lean: `leanprover/lean4:v4.32.0`; mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

## Useful findings first

1. **T09 — reuse an existing generic bound.** `SelectiveCoefficientBounds.half_base_bound_31`
   (203–232) repeats a proof immediately supplied by `half_base_bound` (166–199).
   Instantiate `m := 31`; `4*(31+1)^2=4096` discharges the specialized scale.
   Replace the 24-line proof body at 209–232 by two lines. This preserves all
   hypotheses, the strict half-base conclusion and the exact source encoding.
2. **T01 — expose the sum-of-squares invariant instead of invoking nonlinear
   arithmetic five times.** `ShortSystem.residualSum_zero_iff` (63–88) has a
   23-line proof body (66–88). A two-line conditional `simp only` proof is
   proposed; an eight-line fully explicit fallback avoids depending on the
   conditional simplifier's discharge behavior. Existing lightweight order
   lemmas suffice; do **not** import `Mathlib.NumberTheory.Dioph` just for its
   analogous theorem. `compactResidualSum_zero_iff` already reuses this theorem
   and is not counted as a second independent reduction.
3. **T02 — use finite-set intersection rather than reproving membership.**
   `LowMaskCoding.sum_range_support` (39–46) and
   `MultiTargetCarry.selectedMask_eq` (55–67) independently prove
   `(range n).filter (· ∈ S) = S` by extensionality. Use
   `Finset.filter_mem_eq_inter` and `Finset.inter_eq_right.mpr hS`.
   The local changed spans are 5→2 and 6→3 lines, respectively.
4. **T03 — remove repeated predecessor arithmetic.** Seven local `hpow`
   calculations across `MultiTargetCarry` (40–43,132–135,226–229),
   `SelectiveCarry` (89–92,111–114), and `SelectiveCoefficientBounds`
   (194–197,227–230) use `rw [← pow_succ']; congr 1; omega`.
   Keep each statement and replace its three-line body with
   `rw [← pow_succ', Nat.sub_add_cancel ht]`.
   The mathematical fact already belongs to the power/Nat APIs; an extra
   project lemma is optional, not required. One occurrence is removed entirely
   by T09, so savings must not be added twice.
5. **T05 — one generic residue interface.** The addition/subtraction proofs in
   `CurrentClause2011` (27–39) are duplicated privately in
   `CurrentReflectedGeometry2011` (74–86). Generalize them to `L ∣ n`, place
   them in a low-level module, and retain the old public names as specializations.
   This is primarily a single-maintenance-point improvement, not a large raw
   line-count saving. Do not make geometry import clause merely to borrow the
   lemmas: that needlessly enlarges/can entangle the dependency graph.

## Secondary candidates and tradeoffs

- **T04:** `NativeCyclicConvolution.word_convolution` final factoring step 79–87:
  distributivity plus associativity/commutativity rewrites reduce nine physical
  lines to three. Preserve the explicit modular-congruence argument that precedes
  it; do not attempt to replace the theorem by `ring`.
- **T06:** `NativeRadixDigits.decode_originMask` at 54–57 and 84–86 can use
  the existing `Nat.one_lt_two_pow` instead of deriving a weaker power bound,
  normalizing it, and then calling `omega`. `NativeWindowCarry` already uses
  that existing lemma at63.
- **T07:** `ArithmeticFiniteSwitch.program` at 24–30: retain the equality case;
  in its complement prove the single equivalence
  `tag < count+1 ↔ tag < count` by `omega`, then simplify both conditionals.
  This removes the redundant inner less-than case split (7→4 lines).
- **T08 (optional cosmetic experiment, not recommended by default):**
  `CurrentHighDigits2011.cellDigit_lt` at 80–86 can inspect `cellDigit_formula`
  in two lines. This duplicates finite branch/numeral work already packaged by
  `highDigits_lt`, and may be slower or less clear. Source shortening does not
  establish a performance improvement. Keep the original if profiling or reuse
  favors it.

## Proof engineering policy

- Preserve positive-length instances, Nat-subtraction side conditions, strict
  digit/carry bounds, and the exceptional all-maximum cyclic representation.
  In particular do not turn `word < radix^n-1` into a non-strict inequality or
  assume local no-carry where only a quotient fixed-point construction exists.
- `NativeCyclicCarry` already exposes a well-factored interface:
  `exists_bounded_carries`, `carry_decomposition`, `exists_bounded_digits`,
  `reset_of_bound`. Reuse it rather than add another carry normalizer.
- The existing `decide +kernel` certificates in `CurrentKernel2011` and
  `CurrentReflectedGeometry2011.doubled_control_mass` should not be blindly
  changed to `native_decide`: a source-shortening request is not authorization
  to change trust assumptions. Small finite branch proofs already have compact
  `fin_cases ... <;> decide` forms; factor mathematical families rather than
  replace every proof with broad automation.
- Import narrowing is separate from proof shortening. Eight source files import
  the umbrella `Mathlib.Tactic`; notably `NativeCyclicConvolution:4` and
  `ArithmeticDAG:4`. Candidate module-specific tactic imports must be derived
  from the exact baseline build and checked against all downstream importers.
  Removing an umbrella import may break consumers that relied on its reexports.
  No import patch or compile-time claim is made here.
- Avoid project-wide `[simp]` tags for large concrete kernel, stencil or mask
  definitions. Prefer explicit `simp only` boundaries and small local rewrite
  lemmas; global unfolding can expand enormous expressions downstream.

## Files and verification status

- `PortableCandidates.lean`: isolated generic experiments importing `Mathlib`.
  The broad import is a test harness convenience, **not** a production advice.
- `SourceCandidates.lean`: actual replacement statements for T01, its explicit
  fallback, T09 and cosmetic T08, importing three source modules.
- `replacement_snippets.txt`: exact replacement snippets, including sites not
  easily tested standalone because their original proofs are inside definitions.
- `before_after.md`: exact pinned before blocks and proposed after blocks for
  the ranked changes, generated from the SHA-verified snapshot.
- `findings.json`: structured candidate metadata and conservative counts.
- `mathlib_api/`: pinned primary-source evidence for the APIs. The source
  excerpt verifies names/statements/precedent, not candidate elaboration.

**No Lean compilation or timing was performed for these candidates.** No source
snapshot was edited. Physical source-line counts include nonempty tactic lines
and wrapped proof lines in the displayed changed span, not theorem statements.
They are proposed text reductions, never measured execution-time savings. The
T01 concise and explicit proofs are alternatives; T03/T09 overlap at one site.
